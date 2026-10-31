/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 30 October 2026:
Extract the proof of M093.013 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and prove the published closed statement by introducing its
ten internal binders, then following the original proof unchanged. Import
only the published U013 Statements module; remove the repeated docstring
sentence and omit the source simp registration and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U013.Statements

/-!
# Equal norm subgroups identify classes of the same representative

Proof of the published closed representative equation for the canonical
equivalence between norm quotients with equal norm subgroups.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- An equality of norm subgroups identifies norm classes represented by the same base-field unit. -/
theorem normQuotientEquivOfNormSubgroupEq_normClass :
    NormQuotientEquivOfNormSubgroupEqNormClassStatement.{u} := by
  intro K L M _ _ _ _ _ h x
  change QuotientGroup.quotientMulEquivOfEq h (QuotientGroup.mk x) =
    QuotientGroup.mk x
  exact QuotientGroup.quotientMulEquivOfEq_mk h x

end Langlands.NYLL.LocalFieldTheory
