/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 120, 13 November 2026:
Extract the proof of M128.019 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import only the Basic ValuationStatements module, and
prove the published closed proposition by introducing its six binders.
Since no proof of v_apply (M128.002) is in the Library, the needed
instance is proved as a local fact by the original `rfl` and used in place
of the source rewrite with v_apply. Omit the theorem-only `simp` attribute,
the source noncomputable section and all other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.ValuationStatements

/-!
# Normalized valuation of integral units

A unit of the valuation ring has normalized valuation zero as a field unit.
-/

namespace Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

universe u

open scoped ValuativeRel WithZero

/-- A valuation-integer unit has normalized valuation zero as a field unit. -/
theorem v_integerUnitsToFieldUnits : v_integerUnitsToFieldUnitsStatement.{u} := by
  intro K _ _ _ _ x
  have hxv :
      ValuativeRel.valuation K ((integerUnitsToFieldUnits K x : Kˣ) : K) = 1 := by
    simpa [integerUnitsToFieldUnits] using
      (Valuation.Integers.valuation_unit
        (Valuation.integer.integers (ValuativeRel.valuation K)) x)
  -- The source theorem `v_apply K` (M128.002) at this unit, proved by its original `rfl`.
  have happly :
      v K (Additive.ofMul (integerUnitsToFieldUnits K x)) =
        Multiplicative.toAdd
          (WithZero.unzero
            (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
              (ValuativeRel.valuation K
                ((Additive.toMul (Additive.ofMul (integerUnitsToFieldUnits K x)) : Kˣ) : K)))
            ((map_ne_zero (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).2
              ((Valuation.ne_zero_iff (ValuativeRel.valuation K)).2
                (Additive.toMul (Additive.ofMul (integerUnitsToFieldUnits K x))).ne_zero))) :=
    rfl
  rw [happly]
  apply (WithZero.toAdd_unzero_eq_iff _ 0).2
  change
    (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
        (ValuativeRel.valuation K
          ((integerUnitsToFieldUnits K x : Kˣ) : K)) =
      ((Multiplicative.ofAdd (0 : Int) : Multiplicative Int) :
        WithZero (Multiplicative Int))
  rw [hxv, map_one]
  rfl

end Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField
