/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 120, 13 November 2026:
Extract the proof of M128.006 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import only the Basic ValuationStatements module, and
prove the published closed proposition by introducing its six binders.
Since no proofs of v_mul (M128.004) and v_one (M128.005) are in the
Library, both are proved as local facts by the original proofs of those
theorems (lines 77 and 84-95 of the same source file): v_mul for all pairs
of units, then specialized to x and x⁻¹ as in the source, and v_one. They
are then used by the original rewrite and omega steps. Omit the source
noncomputable section and all other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.ValuationStatements

/-!
# Normalized valuation of an inverse

The normalized valuation of the inverse of a field unit is the negative of
its normalized valuation.
-/

namespace Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

universe u

open scoped ValuativeRel WithZero

/-- The normalized valuation of an inverse is the negative of the original valuation. -/
theorem v_inv : v_invStatement.{u} := by
  intro K _ _ _ _ x
  -- The source theorem `v_mul K` (M128.004), proved by its original `simp` call.
  have hmulGen : ∀ a b : Kˣ,
      v K (Additive.ofMul (a * b)) =
        v K (Additive.ofMul a) + v K (Additive.ofMul b) := by
    intro a b
    simp [v, Valuation.map_mul, WithZero.unzero_mul, toAdd_mul]
  have hmul := hmulGen x x⁻¹
  -- The source proof of `v_one K` (M128.005), inlined.
  have hone : v K (Additive.ofMul (1 : Kˣ)) = 0 := by
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
  rw [mul_inv_cancel, hone] at hmul
  omega

end Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField
