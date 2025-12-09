#pragma once

#include <set>
#include <map>

#include <llvm/Pass.h>
#include <llvm/Analysis/AliasAnalysis.h>
#include <llvm/ADT/BitVector.h>

namespace clou {

  class SecretTaint final : public llvm::FunctionPass {
  public:
    static char ID;
    SecretTaint();

    using TaintMap = std::map<llvm::Instruction *, std::set<llvm::Instruction *>>;

    TaintMap taints;
    std::set<llvm::Instruction *> load_taints;

    void getAnalysisUsage(llvm::AnalysisUsage& AU) const override;
    bool runOnFunction(llvm::Function& F) override;
    void print(llvm::raw_ostream& os, const llvm::Module *M) const override;

    bool secret(llvm::Value *V);

    uint64_t number_of_secrets();

    bool has_secret();

  private:
    uint64_t num_sec;
    // using IdxTaintMap = std::map<llvm::Instruction *, llvm::BitVector>;
  };
  
}
