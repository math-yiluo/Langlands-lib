/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 120, 13 November 2026:
Extract the proof of M128.005 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import only the Basic ValuationStatements module, and
prove the published closed proposition by introducing its five binders
before the original proof. Omit the theorem-only `simp` attribute, the
source noncomputable section and all other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.ValuationStatements

/-!
# Normalized valuation of one

The unit one of a nonarchimedean local field has normalized valuation zero.
-/

namespace Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

universe u

open scoped ValuativeRel WithZero

/-- The normalized valuation of the multiplicative identity is zero. -/
theorem v_one : v_oneStatement.{u} := by
  intro K _ _ _ _
  dsimp [v]
  have hunzero :
      WithZero.unzero
        (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
          (ValuativeRel.valuation K (((1 : Kˣ) : K))))
        ((map_ne_zero (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).2
          ((Valuation.ne_zero_iff (ValuativeRel.valuation K)).2 (Units.ne_zero (1 : Kˣ)))) =
        (1 : Multiplicative Int) := by
    apply WithZero.coe_injective
    simp only [WithZero.coe_unzero, Units.val_one, map_one, WithZero.coe_one]
  rw [hunzero]
  exact toAdd_one

end Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField
