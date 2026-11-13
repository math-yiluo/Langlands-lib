import Langlands.Representation.RankinSelberg.LocalFieldUnequalRankFunctionalEquationStatement
import Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatement

/-!
# From supplied local-field data to the hypothesized normalization

The all-field port states the unequal-rank functional equation for a field `F`
with supplied data `T : LocalFieldData F`, the Borel structures, the residue
cardinality `T.residueCardinality` and the absolute value
`normalizedAbsoluteValue T`. The published target
`LocalFieldUnequalRankFunctionalEquationStatement` instead takes ambient
instances, arbitrary Borel structures, and a hypothesized pair `q`, `abv`
normalized by a uniformizing element `ϖ`. This module shows that the ported
statement at `T := LocalFieldData.ofInstances F`, for every field and every
pair of ranks, implies the target.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg

open MeasureTheory Langlands.HarmonicAnalysis Langlands.Whittaker Langlands.GeneralLinear
  Langlands.QuotientIntegration
open Langlands.GeneralLinear.Iwasawa
open scoped WithZero

universe uF uV uW

section Normalization

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The discrete valuation of the ambient data is the canonical isomorphism
applied to the ambient valuation. -/
theorem discreteValuation_ofInstances (x : F) :
    (LocalFieldData.ofInstances F).discreteValuation x =
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F (ValuativeRel.valuation F x) :=
  rfl

/-- The residue cardinality of the ambient data is the cardinality of the
residue field of the ambient valuation ring. -/
theorem residueCardinality_ofInstances :
    (LocalFieldData.ofInstances F).residueCardinality =
      Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer) :=
  rfl

/-- Equal ambient valuations give equal discrete valuations. -/
theorem discreteValuation_eq_of_valuation_eq {x y : F}
    (h : ValuativeRel.valuation F x = ValuativeRel.valuation F y) :
    (LocalFieldData.ofInstances F).discreteValuation x =
      (LocalFieldData.ofInstances F).discreteValuation y := by
  rw [discreteValuation_ofInstances, discreteValuation_ofInstances, h]

/-- A uniformizing element in the sense of `IsUniformizingElement` has discrete
valuation `exp (-1)`. -/
theorem discreteValuation_of_isUniformizingElement {ϖ : Fˣ}
    (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ) :
    (LocalFieldData.ofInstances F).discreteValuation (ϖ : F) = WithZero.exp (-1) := by
  set T := LocalFieldData.ofInstances F with hT
  obtain ⟨hlt, hpow⟩ := hϖ
  have hu0 : T.uniformizer ≠ 0 := by
    intro h
    have ho := T.ord_uniformizer
    rw [h, T.ord_zero] at ho
    exact zero_ne_one ho
  obtain ⟨m, hm⟩ := hpow T.uniformizer hu0
  have h1 : T.discreteValuation T.uniformizer = T.discreteValuation (ϖ : F) ^ m := by
    rw [← map_zpow₀]
    exact discreteValuation_eq_of_valuation_eq (by rw [hm, map_zpow₀])
  rw [T.discreteValuation_uniformizer] at h1
  have hne : T.discreteValuation (ϖ : F) ≠ 0 :=
    T.discreteValuation.ne_zero_iff.mpr ϖ.ne_zero
  set a := WithZero.log (T.discreteValuation (ϖ : F)) with ha
  have hexp : T.discreteValuation (ϖ : F) = WithZero.exp a := (WithZero.exp_log hne).symm
  have hma : -1 = m * a := by
    rw [hexp, ← WithZero.exp_zsmul, WithZero.exp_inj, smul_eq_mul] at h1
    exact h1
  have hlt' : T.discreteValuation (ϖ : F) < 1 := by
    rw [discreteValuation_ofInstances,
      ← map_one (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F)]
    exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).strictMono hlt
  have ha_neg : a < 0 := by
    rw [hexp, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt'
    exact hlt'
  have hmul : (-m) * a = 1 := by linarith
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hmul with ⟨_, h⟩ | ⟨_, h⟩
  · omega
  · rw [hexp, h]

/-- The order of a uniformizing element is one. -/
theorem ord_of_isUniformizingElement {ϖ : Fˣ}
    (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ) :
    (LocalFieldData.ofInstances F).ord (ϖ : F) = 1 := by
  simp [LocalFieldData.ord, discreteValuation_of_isUniformizingElement hϖ]

/-- An absolute value normalized by a uniformizing element and trivial on
valuation units is the residue-normalized absolute value of the ambient data. -/
theorem eq_normalizedAbsoluteValue_ofInstances (q : ℕ)
    (hq : q = Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer))
    (abv : AbsoluteValue F ℝ) (ϖ : Fˣ)
    (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ)
    (habv : abv (ϖ : F) = (q : ℝ)⁻¹)
    (hunit : ∀ x : F, ValuativeRel.valuation F x = 1 → abv x = 1) :
    abv = normalizedAbsoluteValue (LocalFieldData.ofInstances F) := by
  set T := LocalFieldData.ofInstances F with hT
  have hqT : q = T.residueCardinality := hq.trans residueCardinality_ofInstances.symm
  apply AbsoluteValue.ext
  intro x
  rw [normalizedAbsoluteValue_apply]
  by_cases hx : x = 0
  · simp [hx, T.normalizedAbs_zero]
  obtain ⟨m, hm⟩ := hϖ.2 x hx
  have hϖne : (ϖ : F) ^ m ≠ 0 := zpow_ne_zero m ϖ.ne_zero
  have hvx : ValuativeRel.valuation F x = ValuativeRel.valuation F ((ϖ : F) ^ m) := by
    rw [hm, map_zpow₀]
  -- The normalized side.
  have hord : T.ord x = m := by
    have hdv : T.discreteValuation x = T.discreteValuation ((ϖ : F) ^ m) :=
      discreteValuation_eq_of_valuation_eq hvx
    rw [LocalFieldData.ord, hdv, map_zpow₀, discreteValuation_of_isUniformizingElement hϖ,
      ← WithZero.exp_zsmul, WithZero.log_exp, smul_eq_mul]
    ring
  rw [T.normalizedAbs_of_ne_zero hx, hord, ← hqT]
  -- The hypothesized side.
  set u := x * ((ϖ : F) ^ m)⁻¹ with hu
  have hvu : ValuativeRel.valuation F u = 1 := by
    rw [hu, map_mul, map_inv₀, hvx, mul_inv_cancel₀]
    exact (map_ne_zero _).mpr hϖne
  have hxu : x = u * (ϖ : F) ^ m := by
    rw [hu, mul_assoc, inv_mul_cancel₀ hϖne, mul_one]
  rw [hxu, map_mul, hunit u hvu, one_mul, map_zpow₀, habv, inv_zpow']

end Normalization

/-- The ported all-field statement at the ambient data, for every field and
every pair of ranks, implies the published target with hypothesized `q`,
`abv`, `ϖ` and arbitrary Borel structures. -/
theorem localFieldUnequalRankFunctionalEquation_of_allField
    (h : ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F] (n r : ℕ),
      UnequalRankFunctionalEquationStatement.{uF, uV, uW} F
        (LocalFieldData.ofInstances F) n r) :
    Langlands.RankinSelberg.LocalFieldUnequalRankFunctionalEquationStatement.{uF, uV, uW} := by
  intro F _ _ _ _ _ _ mF hF n r mG hG mU hU mQ hQ q hq abv ϖ hϖ habv hunit hnr ψ hInv μ hμ
    ν hν V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ'
  obtain rfl := hF.measurable_eq
  obtain rfl := hG.measurable_eq
  obtain rfl := hU.measurable_eq
  obtain rfl := hQ.measurable_eq
  have habvT := eq_normalizedAbsoluteValue_ofInstances q hq abv ϖ hϖ habv hunit
  have hqT : q = (LocalFieldData.ofInstances F).residueCardinality :=
    hq.trans residueCardinality_ofInstances.symm
  subst habvT hqT
  have h' := h F n r
  exact @h' hnr ψ hInv μ hμ ν hν V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ'

end Langlands.AllField.RankinSelberg
