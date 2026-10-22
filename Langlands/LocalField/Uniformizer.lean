import Langlands.LocalField.Normalization.Definitions

/-!
# The specified uniformizer as a field unit

These declarations are relocated from `Langlands.LocalFactor.Abelian.Padic`
without changing their public names, types or bodies. Both abelian local factors
and exponent coordinates use the same chosen unit. The historical
`Langlands.LocalFactor.PadicAbelian` namespace is retained for compatibility.
-/

noncomputable section

open scoped WithZero

namespace Langlands.LocalFactor.PadicAbelian

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

private theorem uniformizer_value :
    T.discreteValuation T.uniformizer = WithZero.exp (-1) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  have h : ValuativeRel.valuation F.Carrier T.uniformizer =
      e.symm (WithZero.exp (-1)) :=
    (ValuativeRel.valuation_surjective (e.symm (WithZero.exp (-1)))).choose_spec
  change e (ValuativeRel.valuation F.Carrier T.uniformizer) = WithZero.exp (-1)
  rw [h, e.apply_symm_apply]

/-- The already specified uniformizer, regarded as a field unit.
Its nonzero certificate follows from the actual valuation constructor. -/
def uniformizerUnit : F.Carrierˣ :=
  Units.mk0 T.uniformizer (by
    intro h
    have hv := uniformizer_value T
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm)

@[simp] theorem uniformizerUnit_coe :
    (uniformizerUnit T : F.Carrier) = T.uniformizer := rfl

@[simp] theorem uniformizerUnit_ord :
    T.ord (uniformizerUnit T : F.Carrier) = 1 := by
  simp [PadicField.TopologicalData.ord, uniformizerUnit_coe, uniformizer_value]

theorem uniformizerUnit_zpow_value (n : ℤ) :
    T.discreteValuation ((uniformizerUnit T ^ n : F.Carrierˣ) : F.Carrier) =
      WithZero.exp (-n) := by
  simp [uniformizerUnit, map_zpow₀, uniformizer_value, ← WithZero.exp_zsmul]

theorem uniformizerUnit_zpow_abs (n : ℤ) :
    T.normalizedAbs ((uniformizerUnit T ^ n : F.Carrierˣ) : F.Carrier) =
      (T.residueCardinality : ℝ) ^ (-n) := by
  rw [PadicField.TopologicalData.normalizedAbs, ite_eq_right (Units.ne_zero _)]
  simp only [PadicField.TopologicalData.ord, uniformizerUnit_zpow_value,
    WithZero.log_exp, neg_neg]

end Langlands.LocalFactor.PadicAbelian
