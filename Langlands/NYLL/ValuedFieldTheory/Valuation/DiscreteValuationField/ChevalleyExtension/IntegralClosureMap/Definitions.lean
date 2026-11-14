/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 194 (2026-11-14): extract the listed M110 units
from Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean
at fbd320cd8b1b06487c58227e92eb135794267709; adapt namespace/imports and theorem statements
as documented in the paired Markdown. Source construction bodies are retained.
Original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.U007.Proofs

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation

noncomputable section

universe u v w x y z

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {ΓK : Type w} [LinearOrderedCommGroupWithZero ΓK]

/-- Source M110.025: original construction. -/
def integralClosureToValuationSubringOfHasExtension
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL] :
    integralClosure vK.valuationSubring L →+* vL.valuationSubring where
  toFun z :=
    ⟨(z : L),
      integralClosure_mem_valuationSubring_of_hasExtension
        (L := L) vK vL z⟩
  map_zero' := Subtype.ext rfl
  map_one' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

end

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation
