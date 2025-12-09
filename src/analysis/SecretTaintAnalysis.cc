#include "clou/analysis/SecretTaintAnalysis.h"

#include <map>
#include <set>
#include <cassert>

#include <llvm/IR/Function.h>
#include <llvm/IR/Dominators.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IR/IntrinsicsX86.h>
#include <llvm/Clou/Clou.h>
#include <llvm/ADT/SparseBitVector.h>

#include "clou/util.h"
#include "clou/Mitigation.h"
#include "clou/analysis/NonspeculativeTaintAnalysis.h"
#include "clou/analysis/ConstantAddressAnalysis.h"

// #define DEMO 1
#define DEMO_FUNCTION "param_ptr_demo"
// #define PRINT_NUM_SECRET_VALUES 1
#define PRINT_SEC_VALUES 1
// #define PRINT_TAINTED_INST_EXPANDED 1
#define PRINT_TAINTED_INST 1
// #define PRINT_USERS 1
#define TRACK_PTR_PARAM 1

namespace clou
{

	char SecretTaint::ID = 0;
	SecretTaint::SecretTaint() : llvm::FunctionPass(ID) {}

	void SecretTaint::getAnalysisUsage(llvm::AnalysisUsage &AU) const
	{
		AU.addRequired<ConstantAddressAnalysis>();
		AU.addRequired<llvm::AAResultsWrapperPass>();
		AU.addRequired<NonspeculativeTaint>();
		AU.setPreservesAll();
	}

	static bool isDefinitelyNoAlias(llvm::AliasResult AR)
	{
		switch (AR)
		{
		case llvm::AliasResult::NoAlias:
			return true;
		case llvm::AliasResult::MayAlias:
			return UnsafeAA;
		case llvm::AliasResult::MustAlias:
			return false;
		default:
			std::abort();
		}
	}

	bool SecretTaint::runOnFunction(llvm::Function &F)
	{
#ifdef DEMO
		if (F.getName() != DEMO_FUNCTION) return false;
#endif
        // if ((F.getName() != "main") && (F.getName() != "xmain") && (F.getName() != "xmain.llsct.dup")) {
		//     llvm::errs() << "[Secret Taint] Running on function: " << F.getName() << "\n";
        // }
		auto &AA = getAnalysis<llvm::AAResultsWrapperPass>().getAAResults();
		const auto &CAA = getAnalysis<ConstantAddressAnalysis>();
		llvm::DominatorTree DT(F);
		llvm::LoopInfo LI(DT);

		std::vector<llvm::Instruction *> secret_values;
		for (llvm::CallInst &CI : util::instructions<llvm::CallInst>(F))
		{
			if (llvm::IntrinsicInst *II = llvm::dyn_cast<llvm::IntrinsicInst>(&CI))
			{
				if (II->isAssumeLikeIntrinsic() && II->arg_size() >= 2)
				{
					llvm::Value *AnnotationArg = II->getArgOperand(1)->stripPointerCasts();
					if (llvm::GlobalVariable *strvar = llvm::dyn_cast<llvm::GlobalVariable>(AnnotationArg))
					{
						if (llvm::ConstantDataArray *strData = llvm::dyn_cast<llvm::ConstantDataArray>(strvar->getInitializer()))
						{
							llvm::StringRef annotationCStr = strData->getAsCString();
							if (annotationCStr == "secret")
							{
								llvm::Value *variable = CI.getArgOperand(0)->stripPointerCasts();
								// llvm::errs() << "Secret variable: " << variable->getName() << "\n";
								//  TODO: revisit if this is right or whatever
								if (auto *I = llvm::dyn_cast<llvm::Instruction>(variable))
								{
                                    secret_values.push_back(I); // pushing alloca
#ifdef TRACK_PTR_PARAM
                                    // user of alloca should be store inst
                                    for (llvm::User *U : I->users())
				                    {
					                    if (llvm::StoreInst *store_inst = llvm::dyn_cast<llvm::StoreInst>(U))
					                    {
                                            auto *store_as_inst = llvm::dyn_cast<llvm::Instruction>(store_inst);
                                            // push store inst
                                            if (store_as_inst)
                                                secret_values.push_back(store_as_inst);
                                            // push users of store
                                            for (llvm::User *store_inst_user : store_inst->getValueOperand()->users())
                                            {
                                                if (llvm::Instruction *store_user_as_inst = llvm::dyn_cast<llvm::Instruction>(store_inst_user)) 
                                                {
                                                    if (store_user_as_inst != store_as_inst)
                                                        secret_values.push_back(store_user_as_inst);
                                                }
                                            }
                                        }
                                    }
#endif
								}
							}
						}
					}
				}
			}
		}
#ifdef PRINT_NUM_SECRET_VALUES
		llvm::errs() << "[Secret Taint] # of secret values: " << secret_values.size() << "\n";
#endif
		this->num_sec = secret_values.size();
		if (!has_secret())
			return false;
#ifdef PRINT_SEC_VALUES
        llvm::errs() << "===== Secret Values =====\n";
        for (size_t i=0; i<secret_values.size(); i++) {
            int j = i+1;
            llvm::errs() << j << ") " << *secret_values[i] << "\n";
        }
#endif

#ifdef PRINT_USERS
        llvm::errs() << "===== Secret Value Users =====\n";
        if (secret_values.size() > 0) {
            for (llvm::User *U : secret_values[0]->users()) {
                if (llvm::Instruction *Usr = dyn_cast<llvm::Instruction>(U)) {
                    llvm::errs() << "User instruction: " << *Usr << "\n";
                    llvm::errs() << "  Opcode: " << Usr->getOpcodeName() << "\n";
                    // 3. Print operands
                    for (unsigned i = 0; i < Usr->getNumOperands(); ++i) {
                        llvm::Value *Op = Usr->getOperand(i);
                        llvm::errs() << "    Operand " << i << ": ";
                        Op->print(llvm::errs());
                        llvm::errs() << "\n";
                    }
                    llvm::errs() << "\n";
                }
            }
        }
#endif

		llvm::sort(secret_values);

#if 0
		for (auto &val: secret_values) {
			if (auto *I = llvm::dyn_cast<llvm::Instruction>(val)) {
				llvm::errs() << "secret value type name: " << I->getOpcodeName() << "\n";
			}
		}
#endif

		using Idx = unsigned;
		const auto secret_to_idx = [&secret_values](llvm::Instruction *LI) -> Idx
		{
			const auto it = llvm::lower_bound(secret_values, LI);
			assert(it != secret_values.end() && *it == LI);
			return it - secret_values.begin();
		};
		const auto idx_to_secret = [&secret_values](Idx idx) -> llvm::Instruction *
		{
			assert(idx < secret_values.size());
			return secret_values[idx];
		};

		// Map all stores to any loads (constant or non-constant) which could alias to them
		std::map<llvm::StoreInst *, std::set<llvm::LoadInst *>> rfs;
		for (llvm::StoreInst &SI : util::instructions<llvm::StoreInst>(F))
		{
			auto &loads = rfs[&SI];
			for (llvm::LoadInst &LI : util::instructions<llvm::LoadInst>(F))
				if (!isDefinitelyNoAlias(AA.alias(SI.getPointerOperand(), LI.getPointerOperand())))
					loads.insert(&LI);
		}

		std::map<llvm::Instruction *, llvm::SparseBitVector<>> taints, taints_bak;
		// Taint all of the secret's users for each secret
		//  --> if a store stores to the secret addr (from alloca, keep track of that store instruction)
		for (llvm::Instruction *SecI : secret_values)
		{
            for (llvm::User *U : SecI->users())
            {
                if (llvm::Instruction *Usr = llvm::dyn_cast<llvm::Instruction>(U))
                {
                    // originally store to alloca
                    taints[Usr].set(secret_to_idx(SecI));
                    // users of store val
#if 0
                    if (llvm::StoreInst *store_inst = llvm::dyn_cast<llvm::StoreInst>(Usr))
                    {
                        for (llvm::User *store_val_user : store_inst->getValueOperand()->users())
                        {
                            if (llvm::Instruction *store_val_user_inst = llvm::dyn_cast<llvm::Instruction>(store_val_user)) 
                            {
                                taints[store_val_user_inst].set(secret_to_idx(SecI));
                            }
                        }
                    }
#endif
                }
            }
		}
		do
		{
			taints_bak = taints;

			for (llvm::Instruction &I : llvm::instructions(F))
			{

				// taint secret value instructions with themselves
				if (std::find(secret_values.begin(), secret_values.end(), &I) != secret_values.end())
				{
					taints[&I].set(secret_to_idx(&I));
					continue;
				}

				// TODO: check if load already handled by if not a void type, taint from instructions
				// possible that there are some load instructions we are not handling

				if (llvm::StoreInst *SI = llvm::dyn_cast<llvm::StoreInst>(&I))
				{
					// taint stores whose value is tainted
					if (auto *value_I = llvm::dyn_cast<llvm::Instruction>(SI->getValueOperand()))
					{
						taints[SI] |= taints[value_I];
					}

					// taint every load that could alias with a tainted store
					if (auto *value_I = llvm::dyn_cast<llvm::Instruction>(SI->getValueOperand()))
					{
						const auto &orgs = taints[value_I];
						if (orgs != taints_bak[value_I]) // TODO: This is sound, right?
							for (llvm::LoadInst *LI : rfs[SI])
								taints[LI] |= orgs;
					}
					continue;
				}

				if (llvm::IntrinsicInst *II = llvm::dyn_cast<llvm::IntrinsicInst>(&I))
				{
					if (!II->getType()->isVoidTy() && !II->isAssumeLikeIntrinsic())
					{
						switch (II->getIntrinsicID())
						{
						case llvm::Intrinsic::vector_reduce_add:
						case llvm::Intrinsic::vector_reduce_and:
						case llvm::Intrinsic::vector_reduce_or:
						case llvm::Intrinsic::fshl:
						case llvm::Intrinsic::umax:
						case llvm::Intrinsic::umin:
						case llvm::Intrinsic::ctpop:
						case llvm::Intrinsic::x86_aesni_aeskeygenassist:
						case llvm::Intrinsic::x86_aesni_aesenc:
						case llvm::Intrinsic::x86_aesni_aesenclast:
						case llvm::Intrinsic::bswap:
						case llvm::Intrinsic::x86_pclmulqdq:
						case llvm::Intrinsic::x86_rdrand_32:
						case llvm::Intrinsic::smax:
						case llvm::Intrinsic::smin:
						case llvm::Intrinsic::abs:
						case llvm::Intrinsic::umul_with_overflow:
						case llvm::Intrinsic::bitreverse:
						case llvm::Intrinsic::cttz:
						case llvm::Intrinsic::usub_sat:
						case llvm::Intrinsic::fmuladd:
						case llvm::Intrinsic::fabs:
						case llvm::Intrinsic::floor:
						case llvm::Intrinsic::experimental_constrained_fcmp:
						case llvm::Intrinsic::experimental_constrained_fsub:
						case llvm::Intrinsic::experimental_constrained_fmul:
						case llvm::Intrinsic::experimental_constrained_sitofp:
						case llvm::Intrinsic::experimental_constrained_uitofp:
						case llvm::Intrinsic::experimental_constrained_fcmps:
						case llvm::Intrinsic::experimental_constrained_fadd:
						case llvm::Intrinsic::experimental_constrained_fptosi:
						case llvm::Intrinsic::experimental_constrained_fdiv:
						case llvm::Intrinsic::experimental_constrained_fptoui:
						case llvm::Intrinsic::experimental_constrained_fpext:
						case llvm::Intrinsic::experimental_constrained_floor:
						case llvm::Intrinsic::experimental_constrained_fptrunc:
						case llvm::Intrinsic::experimental_constrained_fmuladd:
						case llvm::Intrinsic::experimental_constrained_ceil:
						case llvm::Intrinsic::masked_load:
						case llvm::Intrinsic::masked_gather:
						case llvm::Intrinsic::fshr:
						case llvm::Intrinsic::stacksave:
						case llvm::Intrinsic::vector_reduce_mul:
						case llvm::Intrinsic::vector_reduce_umax:
						case llvm::Intrinsic::vector_reduce_umin:
						case llvm::Intrinsic::vector_reduce_smax:
						case llvm::Intrinsic::vector_reduce_xor:
						case llvm::Intrinsic::vector_reduce_smin:
						case llvm::Intrinsic::eh_typeid_for:
						case llvm::Intrinsic::uadd_with_overflow:
						case llvm::Intrinsic::ctlz:
						case llvm::Intrinsic::experimental_constrained_powi:
						case llvm::Intrinsic::experimental_constrained_trunc:
						case llvm::Intrinsic::experimental_constrained_round:
						case llvm::Intrinsic::uadd_sat:
							// Passthrough
							for (llvm::Value *arg_V : II->args())
								if (llvm::Instruction *arg_I = llvm::dyn_cast<llvm::Instruction>(arg_V))
									taints[II] |= taints[arg_I];
							break;

						// Note: our annotations are marked as tainted, other annotations are treated as og
						//       and probably has no implications since nothing will depend on the annotation
						case llvm::Intrinsic::annotation:
							if (auto *arg = llvm::dyn_cast<llvm::Instruction>(II->getArgOperand(0)))
								taints[II] |= taints[arg];
							break;

						default:
							warn_unhandled_intrinsic(II);
						}
					}

					continue;
				}

				if (llvm::isa<llvm::CallBase>(&I))
				{
					// Calls never return speculatively tainted values by assumption. We must uphold this.
					continue;
				}

				if (llvm::isa<MitigationInst>(&I))
				{
					continue;
				}

				if (llvm::LoadInst *LI = llvm::dyn_cast<llvm::LoadInst>(&I))
				{
					assert(!LI->getType()->isVoidTy());
				}

				if (!I.getType()->isVoidTy())
				{ // Loads should be tainted here, right?
					// taint if any inputs are tainted
					auto &out = taints[&I];
					for (llvm::Value *op_V : I.operands())
					{
						if (auto *op_I = llvm::dyn_cast<llvm::Instruction>(op_V))
						{
							const auto &in = taints[op_I];
							out |= in;
						}
					}
					continue;
				}
			}

		} while (taints != taints_bak);

// print instructions that are tainted
#ifdef PRINT_TAINTED_INST_EXPANDED
        llvm::errs() << "===== Tainted Inst Expanded =====\n";
        size_t tainted_ctr_exp = 0;
        for (llvm::Instruction &I : llvm::instructions(F)) {
            if (!taints[&I].empty() && !llvm::isa<llvm::BitCastInst>(I)) {
                llvm::errs() << ++tainted_ctr_exp << ") Tainted instruction: " << I << "\n";
                llvm::errs() << "  Opcode: " << I.getOpcodeName() << "\n";
                for (unsigned i = 0; i < I.getNumOperands(); ++i) {
                    llvm::Value *Op = I.getOperand(i);
                    llvm::errs() << "    Operand " << i << ": ";
                    Op->print(llvm::errs());
                    llvm::errs() << "\n";
                }
                llvm::errs() << "\n"; 
            }
        }
#endif

		// Convert back to easy-to-process results.
		this->taints.clear();
		this->load_taints.clear();
		for (const auto &[I, iorgs] : taints)
		{
			auto &orgs = this->taints[I];
			for (Idx idx : iorgs)
				orgs.insert(idx_to_secret(idx));
		}

        // print instructions that are tainted
#ifdef PRINT_TAINTED_INST
        llvm::errs() << "===== Tainted Inst =====\n";
        size_t tainted_ctr = 0;
        for (const auto &it: this->taints) {
			if (it.second.empty()) continue;
            if (llvm::Instruction *I = llvm::dyn_cast<llvm::Instruction>(it.first)) {
                if (!llvm::isa<llvm::BitCastInst>(I)) {
                    llvm::errs() << ++tainted_ctr << ") " << *I << "\n";
                }
            }
        }
#endif

		for (const auto &it: this->taints) {
			if (it.second.empty()) continue;
			// llvm::errs() << "From " << *it.first << "\n";
			if (llvm::LoadInst *LI = llvm::dyn_cast<llvm::LoadInst>(it.first)) {
				if (CAA.isConstantAddress(LI->getPointerOperand())) {
					continue;
				}
				this->load_taints.insert(LI);
			}
			for (auto *I: it.second) {
				// llvm::errs() << "- " << *I << "\n";
				if (llvm::LoadInst *LI = llvm::dyn_cast<llvm::LoadInst>(I)) {
					if (CAA.isConstantAddress(LI->getPointerOperand())) {
						continue;
					}
					this->load_taints.insert(LI);
				}
			}
		}

		return false;
	}

	bool SecretTaint::secret(llvm::Value *V)
	{
		assert(V != nullptr);
		if (auto *I = llvm::dyn_cast<llvm::Instruction>(V))
		{
			return !taints[I].empty();
		}
		else
		{
			return false;
		}
	}

	uint64_t SecretTaint::number_of_secrets()
	{
		return num_sec;
	}

	bool SecretTaint::has_secret()
	{
		return number_of_secrets() > 0;
	}

	void SecretTaint::print(llvm::raw_ostream &os, const llvm::Module *) const
	{
		// For now, just print short summary.
		os << "Tainted instructions:\n";
		for (const auto &[I, sources] : taints)
		{
			if (!sources.empty())
			{
				os << I << " " << *I << "\n";
			}
		}
	}

	static llvm::RegisterPass<SecretTaint> X{"secret-taint", "Secret Taint Analysis Pass", true, true};
	// util::RegisterClangPass<SecretTaint> Y;

}
