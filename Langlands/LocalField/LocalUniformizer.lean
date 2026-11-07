import Langlands.LocalField.LocalFieldArithmetic

/-! # The chosen uniformizer as a unit over an arbitrary local field -/

noncomputable section

open scoped WithZero

namespace Langlands.LocalFactor.LocalAbelian

universe u

variable {F : Type u} [Field F] (T : LocalFieldData F)

private theorem uniformizer_value :
    T.discreteValuation T.uniformizer = WithZero.exp (-1) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  have h : ValuativeRel.valuation F T.uniformizer =
      e.symm (WithZero.exp (-1)) :=
    (ValuativeRel.valuation_surjective (e.symm (WithZero.exp (-1)))).choose_spec
  change e (ValuativeRel.valuation F T.uniformizer) = WithZero.exp (-1)
  rw [h, e.apply_symm_apply]

/-- The already specified uniformizer, regarded as a field unit.
Its nonzero certificate follows from the actual valuation constructor. -/
def uniformizerUnit : Fˣ :=
  Units.mk0 T.uniformizer (by
    intro h
    have hv := uniformizer_value T
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm)

@[simp] theorem uniformizerUnit_coe :
    (uniformizerUnit T : F) = T.uniformizer := rfl

@[simp] theorem uniformizerUnit_ord :
    T.ord (uniformizerUnit T : F) = 1 := by
  simp [LocalFieldData.ord, uniformizerUnit_coe, uniformizer_value]

theorem uniformizerUnit_zpow_value (n : ℤ) :
    T.discreteValuation ((uniformizerUnit T ^ n : Fˣ) : F) =
      WithZero.exp (-n) := by
  simp [uniformizerUnit, map_zpow₀, uniformizer_value, ← WithZero.exp_zsmul]

theorem uniformizerUnit_zpow_abs (n : ℤ) :
    T.normalizedAbs ((uniformizerUnit T ^ n : Fˣ) : F) =
      (T.residueCardinality : ℝ) ^ (-n) := by
  rw [LocalFieldData.normalizedAbs, ite_eq_right (Units.ne_zero _)]
  simp only [LocalFieldData.ord, uniformizerUnit_zpow_value,
    WithZero.log_exp, neg_neg]

end Langlands.LocalFactor.LocalAbelian
