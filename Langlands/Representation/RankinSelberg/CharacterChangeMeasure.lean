import Langlands.Representation.RankinSelberg.CharacterChangeMeasureStatement
import Langlands.Representation.RankinSelberg.UnipotentCharacterChangeModulusStatement
import Langlands.Representation.RankinSelberg.UnipotentCharacterChangeModulusProof
import Langlands.Representation.RankinSelberg.UnipotentQuotient

/-!
# The character-change quotient Haar law from the subgroup modulus

If conjugation by `d_a` pushes unipotent Haar measure forward to `c⁻¹` times
itself, then left translation by `d_a` pushes every compatible quotient measure
forward to `c` times itself. The proof shows that `c⁻¹` times the pushforward
is again compatible and applies quotient-measure uniqueness. The reduction is
then specialized to the canonical p-adic statement, and the published subgroup
law `unipotentCharacterChangeModulus` discharges its hypothesis.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory MeasureTheory.Measure GeneralLinear QuotientIntegration Langlands.Whittaker
open scoped NNReal ENNReal

universe uF

section Conditional

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Conjugation by `d_a` as a homeomorphism of the actual unipotent subgroup. -/
def characterChangeConjHomeomorph (a : Fˣ) (n : ℕ) :
    upperUnipotent (n + 1) F ≃ₜ upperUnipotent (n + 1) F where
  toFun := characterChangeConj a n
  invFun := characterChangeConj a⁻¹ n
  left_inv u := by
    apply Subtype.ext
    simp only [characterChangeConj_val, ← characterChangeElement_inv, inv_inv, mul_assoc,
      inv_mul_cancel_left, inv_mul_cancel, mul_one]
  right_inv u := by
    apply Subtype.ext
    simp only [characterChangeConj_val, ← characterChangeElement_inv, inv_inv, mul_assoc,
      mul_inv_cancel_left, mul_inv_cancel, mul_one]
  continuous_toFun := by
    change Continuous fun u : upperUnipotent (n + 1) F => characterChangeConj a n u
    exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun := by
    change Continuous fun u : upperUnipotent (n + 1) F => characterChangeConj a⁻¹ n u
    exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

variable (n : ℕ)

/-- Character change commutes with right translation on the quotient. -/
theorem rightTranslate_comp_characterChangeQuotient (a : Fˣ)
    (g : Langlands.GeneralLinear (n + 1) F) :
    (rightTranslate (upperUnipotent (n + 1) F) g) ∘ (characterChangeQuotient a n) =
      (characterChangeQuotient a n) ∘ (rightTranslate (upperUnipotent (n + 1) F) g) := by
  funext q
  induction q using Quotient.inductionOn with
  | h x =>
    simp only [Function.comp_apply, characterChangeQuotient_mk, rightTranslate_mk, mul_assoc]

variable [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]

/-- The orbital average of `f` at `N d_a g` is `c` times the orbital average of
the left translate `x ↦ f (d_a x)` at `N g`, given the subgroup modulus. -/
theorem quotientAverage_characterChangeQuotient (abv : AbsoluteValue F ℝ) (a : Fˣ)
    (hN : Measure.map (characterChangeConj a n) (unipotentHaar F n) =
      ((characterChangeModulus abv a n : ℝ≥0∞)⁻¹) • unipotentHaar F n)
    (f : Langlands.GeneralLinear (n + 1) F → ℂ) (q : LeftUnipotentQuotient n F) :
    quotientAverage (upperUnipotent (n + 1) F) (unipotentHaar F n) f
        (characterChangeQuotient a n q) =
      (characterChangeModulus abv a n : ℂ) *
        quotientAverage (upperUnipotent (n + 1) F) (unipotentHaar F n)
          (fun x => f (characterChangeElement a n * x)) q := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [characterChangeQuotient_mk, quotientAverage_mk, quotientAverage_mk]
    set d := characterChangeElement a n
    set c := characterChangeModulus abv a n
    let e := (characterChangeConjHomeomorph (F := F) a n).toMeasurableEquiv
    have hconj : (fun v : upperUnipotent (n + 1) F => f (d * (v.val * g))) =
        fun v => f ((e v).val * (d * g)) := by
      funext v
      change f (d * (v.val * g)) = f ((d * v.val * d⁻¹) * (d * g))
      simp only [mul_assoc, inv_mul_cancel_left]
    have hmap : (∫ v, f ((e v).val * (d * g)) ∂unipotentHaar F n) =
        ((c : ℝ≥0∞)⁻¹).toReal • ∫ u, f (u.val * (d * g)) ∂unipotentHaar F n := by
      rw [← integral_map_equiv e (fun u : upperUnipotent (n + 1) F => f (u.val * (d * g)))]
      change (∫ u, f (u.val * (d * g)) ∂Measure.map (characterChangeConj a n)
        (unipotentHaar F n)) = _
      rw [hN, integral_smul_measure]
    rw [hconj, hmap]
    have hc : (c : ℝ) ≠ 0 := by exact_mod_cast characterChangeModulus_ne_zero abv a n
    rw [ENNReal.toReal_inv, ENNReal.coe_toReal, Complex.real_smul, ← mul_assoc]
    push_cast
    rw [mul_inv_cancel₀ (by exact_mod_cast hc), one_mul]

variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
variable [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]

/-- Given the subgroup modulus, `c⁻¹` times the character-change pushforward of a
compatible quotient measure is again compatible with the same Haar measures. -/
theorem isCompatible_smul_map_characterChangeQuotient (abv : AbsoluteValue F ℝ) (a : Fˣ)
    (hN : Measure.map (characterChangeConj a n) (unipotentHaar F n) =
      ((characterChangeModulus abv a n : ℝ≥0∞)⁻¹) • unipotentHaar F n)
    (μ : Measure (LeftUnipotentQuotient n F))
    (hμ : IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
      (unipotentHaar F n) μ) :
    IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n) (unipotentHaar F n)
      (((characterChangeModulus abv a n : ℝ≥0∞)⁻¹) •
        Measure.map (characterChangeQuotient a n) μ) := by
  set c := characterChangeModulus abv a n
  set e := characterChangeQuotient (F := F) a n
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast characterChangeModulus_ne_zero abv a n
  have hcinv0 : (c : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top
  have hcinvtop : (c : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hc0
  have hd : ∀ f : Langlands.GeneralLinear (n + 1) F → ℂ, Continuous f → HasCompactSupport f →
      Continuous (fun x => f (characterChangeElement a n * x)) ∧
        HasCompactSupport (fun x => f (characterChangeElement a n * x)) := fun f hf hcs =>
    ⟨hf.comp (continuous_const.mul continuous_id),
      hcs.comp_homeomorph (Homeomorph.mulLeft (characterChangeElement a n))⟩
  have havg : ∀ f : Langlands.GeneralLinear (n + 1) F → ℂ,
      (quotientAverage (upperUnipotent (n + 1) F) (unipotentHaar F n) f) ∘ e =
        fun q => (c : ℂ) * quotientAverage (upperUnipotent (n + 1) F) (unipotentHaar F n)
          (fun x => f (characterChangeElement a n * x)) q := fun f => by
    funext q
    exact quotientAverage_characterChangeQuotient n abv a hN f q
  refine
    { nonzero := ?_
      regular := ?_
      right_invariant := ?_
      averaging_integrable := ?_
      integral_formula := ?_ }
  · intro h
    apply hμ.nonzero
    apply (Measure.map_eq_zero_iff e.continuous.measurable.aemeasurable).mp
    have h' := congrArg ((c : ℝ≥0∞) • ·) h
    simpa only [smul_smul, ENNReal.mul_inv_cancel hc0 ENNReal.coe_ne_top, one_smul,
      smul_zero] using h'
  · have := hμ.regular
    have : (Measure.map e μ).Regular := Measure.Regular.map e
    exact Measure.Regular.smul hcinvtop
  · intro g
    refine ⟨(rightTranslate _ g).continuous.measurable, ?_⟩
    rw [Measure.map_smul, Measure.map_map (rightTranslate _ g).continuous.measurable
      e.continuous.measurable, rightTranslate_comp_characterChangeQuotient,
      ← Measure.map_map e.continuous.measurable (rightTranslate _ g).continuous.measurable,
      (hμ.right_invariant g).map_eq]
    exact (rightTranslate _ g).continuous.measurable.aemeasurable
  · intro f hf hcs
    apply Integrable.smul_measure _ hcinvtop
    change Integrable _ (Measure.map e.toMeasurableEquiv μ)
    rw [integrable_map_equiv]
    change Integrable ((quotientAverage (upperUnipotent (n + 1) F) (unipotentHaar F n) f) ∘ e) μ
    rw [havg]
    exact (hμ.averaging_integrable _ (hd f hf hcs).1 (hd f hf hcs).2).const_mul _
  · intro f hf hcs
    rw [integral_smul_measure]
    change ((c : ℝ≥0∞)⁻¹).toReal •
      (∫ q, quotientAverage (upperUnipotent (n + 1) F) (unipotentHaar F n) f q
        ∂Measure.map e.toMeasurableEquiv μ) = _
    rw [integral_map_equiv]
    change ((c : ℝ≥0∞)⁻¹).toReal •
      (∫ q, ((quotientAverage (upperUnipotent (n + 1) F) (unipotentHaar F n) f) ∘ e) q ∂μ) = _
    rw [havg, integral_const_mul, hμ.integral_formula _ (hd f hf hcs).1 (hd f hf hcs).2,
      integral_mul_left_eq_self f (characterChangeElement a n)]
    have hc : (c : ℝ) ≠ 0 := by exact_mod_cast characterChangeModulus_ne_zero abv a n
    rw [ENNReal.toReal_inv, ENNReal.coe_toReal, Complex.real_smul, ← mul_assoc]
    push_cast
    rw [inv_mul_cancel₀ (by exact_mod_cast hc), one_mul]

/-- The subgroup modulus `c⁻¹` implies the quotient law with the positive factor
`c`, for every compatible quotient measure. -/
theorem hasCharacterChangeMeasureLaw_of_unipotentModulus (abv : AbsoluteValue F ℝ) (a : Fˣ)
    (hN : Measure.map (characterChangeConj a n) (unipotentHaar F n) =
      ((characterChangeModulus abv a n : ℝ≥0∞)⁻¹) • unipotentHaar F n)
    (μ : Measure (LeftUnipotentQuotient n F))
    (hμ : IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
      (unipotentHaar F n) μ) :
    HasCharacterChangeMeasureLaw abv a μ := by
  set c := characterChangeModulus abv a n
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast characterChangeModulus_ne_zero abv a n
  have h : ((c : ℝ≥0∞)⁻¹) • Measure.map (characterChangeQuotient a n) μ = μ :=
    (unipotentQuotientHaar_unique F n _
      (isCompatible_smul_map_characterChangeQuotient n abv a hN μ hμ)).trans
      (unipotentQuotientHaar_unique F n μ hμ).symm
  unfold HasCharacterChangeMeasureLaw
  calc Measure.map (characterChangeQuotient a n) μ
      = ((c : ℝ≥0∞) * (c : ℝ≥0∞)⁻¹) • Measure.map (characterChangeQuotient a n) μ := by
        rw [ENNReal.mul_inv_cancel hc0 ENNReal.coe_ne_top, one_smul]
    _ = (c : ℝ≥0∞) • μ := by rw [← smul_smul, h]

end Conditional

/-- The subgroup modulus statement implies the canonical quotient law. -/
theorem characterChangeCompatibleMeasure_of_unipotentModulus
    (hN : UnipotentCharacterChangeModulusStatement.{uF}) :
    CharacterChangeCompatibleMeasureStatement.{uF} := by
  intro p _ F T n a
  let _ := T.topology
  let _ := T.valuativeRel
  let _ := T.localField
  let _ := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let _ : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let _ := borel (upperUnipotent (n + 1) F.Carrier)
  let _ : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let _ := borel (LeftUnipotentQuotient n F.Carrier)
  let _ : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  exact fun μ hμ => hasCharacterChangeMeasureLaw_of_unipotentModulus n
    (normalizedAbsoluteValue T) a (hN p F T n a) μ hμ

/-- Left translation by `d_a` multiplies every compatible quotient measure by the
canonical character-change modulus. -/
theorem characterChangeCompatibleMeasure :
    CharacterChangeCompatibleMeasureStatement.{uF} :=
  characterChangeCompatibleMeasure_of_unipotentModulus unipotentCharacterChangeModulus

end Langlands.RankinSelberg
