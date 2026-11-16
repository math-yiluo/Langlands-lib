/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 328, 2026-11-16: extract only the proof of M391.008,
lines 113–118, from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
use the Langlands.NYLL namespace and exact published closed Prop target,
replace the source imports by its statement module, and replace the
M388.002 wrapper by the underlying Mathlib coercion formula. Preserve the
source's simp behavior through a private specialization of the exact proof.
See the paired Markdown for the full adaptation record and licenses/NYLL/
for the retained license and notice.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer.UnitFactorFieldUnitCoeStatement

/-!
# Coercion of a valuation-ring unit included in the field

The exact proof of NYLL M391.008, using the published unit-factor map.
-/

universe u v

namespace Langlands.NYLL.LubinTate

/-- The unit-factor inclusion has the expected underlying field element. -/
theorem standardLubinTateUnitFactorFieldUnit_coe :
    standardLubinTateUnitFactorFieldUnit_coeStatement.{u, v} := by
  intro K _ F a
  exact ValuationSubring.coe_unitGroupMulEquiv_symm_apply _ a

/-- Register the source coercion rule from the exact closed-target proof. -/
@[simp]
private theorem standardLubinTateUnitFactorFieldUnit_coe_apply
    {K : Type u} [Field K]
    (F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K)
    (a : F.valuationSubringˣ) :
    (standardLubinTateUnitFactorFieldUnit F a : K) =
      (a : F.valuationSubring) :=
  standardLubinTateUnitFactorFieldUnit_coe F a

end Langlands.NYLL.LubinTate
