import Langlands.Representation.Conductor.SphericalMinusculeTranslation

/-! # Integrated minuscule translation of actual spherical coefficients -/

noncomputable section

namespace Langlands.Conductor

open MeasureTheory Langlands.GeneralLinear Langlands.Whittaker
open Langlands.GeneralLinear.Iwasawa Langlands.RankinSelberg
open Langlands.QuotientIntegration Langlands.HarmonicAnalysis
open Langlands.Unramified.MinusculeCosets
open Langlands.Whittaker.UpperUnipotentCharacter (adjacentUnit)
open scoped BigOperators

universe uF uV uΛ

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F] {n : ℕ}
variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
variable [MeasurableSpace (upperUnipotent (n + 1) F)]
  [BorelSpace (upperUnipotent (n + 1) F)]
variable [MeasurableSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)]
variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
variable {ϖ : Fˣ} {μ : Measure (LeftUnipotentQuotient n F)}
variable (h : IsJacquetNormalization q ψ abv ϖ μ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
variable (hπ : IsSmooth π) (ℓ : glFunctionals ψ (n + 1) π)
variable {Λ : Type uΛ} [Fintype Λ]
variable (hq : 0 < q) (hcard : Fintype.card Λ = q)
variable (hgeneric : ∀ i : Fin n, ∃ x : F,
  (ValuativeRel.valuation F) x * (ValuativeRel.valuation F) (ϖ : F) ≤ 1 ∧
    inverseStandardCharacter ψ n (adjacentUnit i x) ≠ 1)
variable (σ : Λ → F)
variable (hσ : ∀ x, σ x ∈ (ValuativeRel.valuation F).integer)
variable (hinj : ∀ x y, (ValuativeRel.valuation F) (σ x - σ y) < 1 → x = y)
variable (hsurj : ∀ z ∈ (ValuativeRel.valuation F).integer,
  ∃ x, (ValuativeRel.valuation F) (z - σ x) < 1)

private theorem modelCoefficient_evaluation_as_integral
    (w : (coefficientModel π ℓ).toSubmodule)
    (x : Fin (n + 1) → ℂˣ) (d : ℤ) :
    symmetricTorusEvaluation (Fin (n + 1)) ℂ x
      (degreeCorankOneModelCoefficient h π hπ ℓ w d) =
    ∫ t, symmetricTorusEvaluation (Fin (n + 1)) ℂ x
      (degreeCorankOneModelIntegrand h π ℓ w d t) ∂μ := by
  simpa only [degreeCorankOneModelIntegrand,
    symmetricTorusEvaluation_degreeCorankOnePolynomialIntegrand] using
    symmetricTorusEvaluation_degreeCorankOneModelCoefficient h π hπ ℓ w x d

include hq hcard hgeneric hσ hinj hsurj in
/-- Integrate the actual finite sum after a separate right-translation
change of variables for each minuscule representative. -/
theorem degreeCorankOneModelCoefficient_minusculeTranslate
    (k : ℕ) (w : (coefficientModel π ℓ).toSubmodule) (d : ℤ) :
    degreeCorankOneModelCoefficient h π hπ ℓ
      (corankOneMinusculeTranslate abv π ℓ ϖ σ k w) d =
      symmetricTorusHeckeScalar n q k *
        degreeCorankOneModelCoefficient h π hπ ℓ w (d - k) := by
  classical
  let : BorelSpace (LeftUnipotentQuotient n F) := h.borel
  rw [corankOneMinusculeTranslate_apply]
  change (degreeCorankOneModelCoefficientLinearMap h π hπ ℓ d)
      (∑ a : CosetIndex Λ (n + 1) k,
        corankOneInverseTranslate abv π ℓ (labelledRep ϖ σ a) w) = _
  rw [map_sum]
  change (∑ a : CosetIndex Λ (n + 1) k,
    degreeCorankOneModelCoefficient h π hπ ℓ
      (corankOneInverseTranslate abv π ℓ (labelledRep ϖ σ a) w) d) = _
  apply symmetricTorus_eq_of_evaluations
  intro x
  simp only [map_sum, map_mul]
  simp_rw [modelCoefficient_evaluation_as_integral]
  let f (a : CosetIndex Λ (n + 1) k) (t : LeftUnipotentQuotient n F) : ℂ :=
    symmetricTorusEvaluation (Fin (n + 1)) ℂ x
      (degreeCorankOneModelIntegrand h π ℓ
        (corankOneInverseTranslate abv π ℓ (labelledRep ϖ σ a) w) d
          (rightTranslate (upperUnipotent (n + 1) F) (labelledRep ϖ σ a) t))
  have hf (a : CosetIndex Λ (n + 1) k) : Integrable (f a) μ :=
    (h.measure.right_invariant (labelledRep ϖ σ a)).integrable_comp_of_integrable
      (degreeCorankOneModelIntegrand_evaluation_integrable h π hπ ℓ
        (corankOneInverseTranslate abv π ℓ (labelledRep ϖ σ a) w) x d)
  calc
    _ = ∑ a : CosetIndex Λ (n + 1) k, ∫ t, f a t ∂μ := by
      apply Finset.sum_congr rfl
      intro a _
      exact ((h.measure.right_invariant (labelledRep ϖ σ a)).integral_comp
        (rightTranslate (upperUnipotent (n + 1) F)
          (labelledRep ϖ σ a)).measurableEmbedding _).symm
    _ = ∫ t, ∑ a : CosetIndex Λ (n + 1) k, f a t ∂μ :=
      (integral_finsetSum _ (fun a _ => hf a)).symm
    _ = ∫ t, symmetricTorusEvaluation (Fin (n + 1)) ℂ x
        (symmetricTorusHeckeScalar n q k *
          degreeCorankOneModelIntegrand h π ℓ w (d - k) t) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [f, ← map_sum]
      congr 1
      exact sum_degreeCorankOnePolynomialIntegrand_inverseTranslate
        abv π ℓ h.uniformizer q h.conductor.1 hq hcard hgeneric σ hσ hinj hsurj k w d t
    _ = _ := by
      simp only [map_mul]
      exact integral_const_mul _ _

include hq hcard hgeneric hσ hinj hsurj

theorem corankOneModelLaurentSeries_minusculeTranslate
    (k : ℕ) (w : (coefficientModel π ℓ).toSubmodule) :
    corankOneModelLaurentSeries h π hπ ℓ
      (corankOneMinusculeTranslate abv π ℓ ϖ σ k w) =
      HahnSeries.single (k : ℤ) (symmetricTorusHeckeScalar n q k) *
        corankOneModelLaurentSeries h π hπ ℓ w := by
  apply HahnSeries.ext
  funext d
  simp only [HahnSeries.coeff_single_mul, corankOneModelLaurentSeries_coeff]
  exact degreeCorankOneModelCoefficient_minusculeTranslate h π hπ ℓ hq hcard
    hgeneric σ hσ hinj hsurj k w d

theorem corankOneModelDenominatorProduct_minusculeTranslate
    (k : ℕ) (w : (coefficientModel π ℓ).toSubmodule) (P : Polynomial ℂ) :
    corankOneModelDenominatorProduct h π hπ ℓ
      (corankOneMinusculeTranslate abv π ℓ ϖ σ k w) P =
      HahnSeries.single (k : ℤ) (symmetricTorusHeckeScalar n q k) *
        corankOneModelDenominatorProduct h π hπ ℓ w P := by
  simp only [corankOneModelDenominatorProduct,
    corankOneModelLaurentSeries_minusculeTranslate h π hπ ℓ hq hcard
      hgeneric σ hσ hinj hsurj, mul_assoc]

theorem corankOneModelDenominatorProduct_minusculeTranslate_support_finite
    (k : ℕ) (w : (coefficientModel π ℓ).toSubmodule) (P : Polynomial ℂ)
    (hw : (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite) :
    (corankOneModelDenominatorProduct h π hπ ℓ
      (corankOneMinusculeTranslate abv π ℓ ϖ σ k w) P).support.Finite := by
  rw [corankOneModelDenominatorProduct_minusculeTranslate h π hπ ℓ hq hcard
    hgeneric σ hσ hinj hsurj]
  exact laurentSingleMul_support_finite _ hw _ _

/-- The actual weighted model action restricts to finite-support vectors. -/
def corankOneFiniteSupportMinusculeTranslate (P : Polynomial ℂ) (k : ℕ) :
    Module.End ℂ (corankOneFiniteSupportModelVectors h π hπ ℓ P) where
  toFun w := ⟨corankOneMinusculeTranslate abv π ℓ ϖ σ k w.val,
    corankOneModelDenominatorProduct_minusculeTranslate_support_finite
      h π hπ ℓ hq hcard hgeneric σ hσ hinj hsurj k w.val P w.property⟩
  map_add' w z := by
    apply Subtype.ext
    exact (corankOneMinusculeTranslate abv π ℓ ϖ σ k).map_add w.val z.val
  map_smul' a w := by
    apply Subtype.ext
    exact (corankOneMinusculeTranslate abv π ℓ ϖ σ k).map_smul a w.val

@[simp] theorem corankOneFiniteSupportMinusculeTranslate_apply
    (P : Polynomial ℂ) (k : ℕ)
    (w : corankOneFiniteSupportModelVectors h π hπ ℓ P) :
    (corankOneFiniteSupportMinusculeTranslate h π hπ ℓ hq hcard
      hgeneric σ hσ hinj hsurj P k w).val =
      corankOneMinusculeTranslate abv π ℓ ϖ σ k w.val := rfl

/-- The degree shift disappears when summing the actual finite coefficients. -/
theorem corankOneModelNumerator_minusculeTranslate
    (k : ℕ) (w : (coefficientModel π ℓ).toSubmodule) (P : Polynomial ℂ)
    (hw : (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite)
    (htw : (corankOneModelDenominatorProduct h π hπ ℓ
      (corankOneMinusculeTranslate abv π ℓ ϖ σ k w) P).support.Finite) :
    corankOneModelNumerator h π hπ ℓ
      (corankOneMinusculeTranslate abv π ℓ ϖ σ k w) P htw =
      symmetricTorusHeckeScalar n q k * corankOneModelNumerator h π hπ ℓ w P hw := by
  unfold corankOneModelNumerator
  simp only [corankOneModelDenominatorProduct_minusculeTranslate h π hπ ℓ hq hcard
    hgeneric σ hσ hinj hsurj]
  exact finiteLaurentCoefficientSum_single_mul _ hw _ _ _

theorem corankOneModelNumeratorLinearMap_minusculeTranslate
    (P : Polynomial ℂ) (k : ℕ)
    (w : corankOneFiniteSupportModelVectors h π hπ ℓ P) :
    corankOneModelNumeratorLinearMap h π hπ ℓ P
      (corankOneFiniteSupportMinusculeTranslate h π hπ ℓ hq hcard
        hgeneric σ hσ hinj hsurj P k w) =
      symmetricTorusHeckeScalar n q k * corankOneModelNumeratorLinearMap h π hπ ℓ P w := by
  exact corankOneModelNumerator_minusculeTranslate h π hπ ℓ hq hcard
    hgeneric σ hσ hinj hsurj k w.val P w.property _

theorem heckeScalar_mul_mem_numeratorSubmodule
    (P : Polynomial ℂ) (k : ℕ) (a : symmetricTorusSubalgebra (Fin (n + 1)) ℂ)
    (ha : a ∈ corankOneModelNumeratorSubmodule h π hπ ℓ P) :
    symmetricTorusHeckeScalar n q k * a ∈
      corankOneModelNumeratorSubmodule h π hπ ℓ P := by
  obtain ⟨w, hw, rfl⟩ :=
    (mem_corankOneModelNumeratorSubmodule_iff h π hπ ℓ P a).mp ha
  have htw := corankOneModelDenominatorProduct_minusculeTranslate_support_finite
    h π hπ ℓ hq hcard hgeneric σ hσ hinj hsurj k w P hw
  apply (mem_corankOneModelNumeratorSubmodule_iff h π hπ ℓ P _).mpr
  exact ⟨corankOneMinusculeTranslate abv π ℓ ϖ σ k w, htw,
    corankOneModelNumerator_minusculeTranslate h π hπ ℓ hq hcard
      hgeneric σ hσ hinj hsurj k w P hw htw⟩

/-- The actual numerator image is stable under every elementary symmetric
Laurent polynomial. The nonzero square-root normalization is absorbed by
its complex vector-space structure. -/
theorem elementary_mul_mem_numeratorSubmodule
    (P : Polynomial ℂ) (k : ℕ) (a : symmetricTorusSubalgebra (Fin (n + 1)) ℂ)
    (ha : a ∈ corankOneModelNumeratorSubmodule h π hπ ℓ P) :
    symmetricTorusElementary (n + 1) k * a ∈
      corankOneModelNumeratorSubmodule h π hπ ℓ P := by
  have hm := heckeScalar_mul_mem_numeratorSubmodule h π hπ ℓ hq hcard
    hgeneric σ hσ hinj hsurj P k a ha
  let c : ℂ := (Real.sqrt (q : ℝ) : ℂ) ^ (k * (n + 1 - k))
  have hc : c ≠ 0 := pow_ne_zero _
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hq)).ne')
  have hs := (corankOneModelNumeratorSubmodule h π hπ ℓ P).smul_mem c⁻¹ hm
  simpa only [symmetricTorusHeckeScalar, c, Algebra.smul_def, ← mul_assoc,
    ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul] using hs

end Langlands.Conductor
