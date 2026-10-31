/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 1097, 30 October 2026:
Extract the proof of M093.011 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and prove the published closed statement by introducing its
eight internal binders, then following the original proof unchanged. Import
only the published U011 Statements module; omit the source simp registration
and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U011.Statements

/-!
# The subgroup-equality norm-quotient equivalence on representatives

Proof of the published closed proposition that the equivalence from the norm
quotient to the quotient by an equal subgroup sends the norm class of a unit to
the class of the same unit.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- After identifying the norm subgroup with another subgroup, a norm class maps to the
corresponding quotient class. -/
theorem normQuotientEquivOfSubgroupEq_normClass :
    NormQuotientEquivOfSubgroupEqNormClassStatement.{u} := by
  intro K L _ _ _ N h x
  change QuotientGroup.quotientMulEquivOfEq h (QuotientGroup.mk x) =
    QuotientGroup.mk x
  exact QuotientGroup.quotientMulEquivOfEq_mk h x

end Langlands.NYLL.LocalFieldTheory
