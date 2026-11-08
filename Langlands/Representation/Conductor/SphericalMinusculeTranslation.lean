import Langlands.Representation.Conductor.SphericalHecke
import Langlands.Representation.Conductor.SphericalNumeratorTranslation

/-! # Weighted inverse minuscule translation of actual model vectors -/

noncomputable section

namespace Langlands.Conductor

open MeasureTheory Langlands.GeneralLinear Langlands.Whittaker
open Langlands.GeneralLinear.Iwasawa Langlands.RankinSelberg
open Langlands.QuotientIntegration Langlands.HarmonicAnalysis
open Langlands.Unramified.MinusculeCosets
open Langlands.Whittaker.UpperUnipotentCharacter (adjacentUnit)
open scoped BigOperators

universe uF uΓ uΛ uV

section Degree

variable {F : Type uF} [Field F] {Γ₀ : Type uΓ} [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation F Γ₀} {n : ℕ} {ϖ : Fˣ}

theorem det_torus_eq_zpow_sum (lam : Fin (n + 1) → ℤ) :
    (torus ϖ lam : Matrix (Fin (n + 1)) (Fin (n + 1)) F).det =
      (ϖ : F) ^ (∑ i, lam i) := by
  change (Matrix.diagonal fun i => ((ϖ ^ lam i : Fˣ) : F)).det = _
  rw [Matrix.det_diagonal]
  simp only [Units.val_zpow_eq_zpow_val]
  exact prod_zpow_eq_zpow_sum Finset.univ ϖ lam

theorem valuation_det_eq_zpow_sum_exponent (hϖ : IsUniformizingElement v ϖ)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    v (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F).det =
      v (ϖ : F) ^ (∑ i, exponent hϖ g i) := by
  obtain ⟨c, hc, hg⟩ := exists_eq_unipotentPart hϖ g
  conv_lhs => rw [hg]
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, map_mul]
  rw [det_eq_one_of_mem_upperUnipotent (unipotentPart hϖ g).property,
    map_one, one_mul, valuation_det_eq_one hc, mul_one,
    det_torus_eq_zpow_sum, map_zpow₀]

theorem sum_exponent_mul (hϖ : IsUniformizingElement v ϖ)
    (g r : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    (∑ i, exponent hϖ (g * r) i) =
      (∑ i, exponent hϖ g i) + ∑ i, exponent hϖ r i := by
  apply (zpow_right_strictAnti₀ (valuation_pos v ϖ) hϖ.1).injective
  change v (ϖ : F) ^ (∑ i, exponent hϖ (g * r) i) =
    v (ϖ : F) ^ ((∑ i, exponent hϖ g i) + ∑ i, exponent hϖ r i)
  rw [← valuation_det_eq_zpow_sum_exponent hϖ,
    Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, map_mul,
    valuation_det_eq_zpow_sum_exponent hϖ, valuation_det_eq_zpow_sum_exponent hϖ,
    zpow_add₀ (valuation_pos v ϖ).ne']

theorem sum_exponent_labelledRep (hϖ : IsUniformizingElement v ϖ)
    {Λ : Type uΛ} (σ : Λ → F) {k : ℕ} (a : CosetIndex Λ (n + 1) k) :
    (∑ i, exponent hϖ (labelledRep ϖ σ a) i) = k := by
  rw [labelledRep, cosetRep,
    exponent_unipotent_mul hϖ _ (radicalElement_mem_upperUnipotent _ _),
    exponent_torus]
  simp only [subsetExponent]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
    mul_one, a.1.property]

end Degree

section Model

variable {F : Type uF} [Field F] [TopologicalSpace F]
variable {ψ : UnitaryAdditiveCharacter F} {n : ℕ}
variable (abv : AbsoluteValue F ℝ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
variable (ℓ : glFunctionals ψ (n + 1) π)
variable {Λ : Type uΛ} [Fintype Λ] (ϖ : Fˣ) (σ : Λ → F)

/-- The inverse model translate weighted to cancel the determinant weight
after the quotient change of variables. -/
def corankOneInverseTranslate (r : Langlands.GeneralLinear (n + 1) F) :
    Module.End ℂ (coefficientModel π ℓ).toSubmodule :=
  (determinantWeight abv r (0 - 1 / 2))⁻¹ •
    modelRepresentation π ℓ (rankInclusion 1 r⁻¹)

@[simp] theorem corankOneInverseTranslate_restriction
    (r g : Langlands.GeneralLinear (n + 1) F)
    (w : (coefficientModel π ℓ).toSubmodule) :
    (corankOneInverseTranslate abv π ℓ r w).val.val (rankInclusion 1 (g * r)) =
      (determinantWeight abv r (0 - 1 / 2))⁻¹ *
        w.val.val (rankInclusion 1 g) := by
  change (determinantWeight abv r (0 - 1 / 2))⁻¹ *
      w.val.val (rankInclusion 1 (g * r) * rankInclusion 1 r⁻¹) = _
  rw [← map_mul, mul_inv_cancel_right]

/-- The actual finite weighted inverse minuscule sum on the model of `π`. -/
def corankOneMinusculeTranslate (k : ℕ) :
    Module.End ℂ (coefficientModel π ℓ).toSubmodule :=
  ∑ a : CosetIndex Λ (n + 1) k,
    corankOneInverseTranslate abv π ℓ (labelledRep ϖ σ a)

theorem corankOneMinusculeTranslate_apply (k : ℕ)
    (w : (coefficientModel π ℓ).toSubmodule) :
    corankOneMinusculeTranslate abv π ℓ ϖ σ k w =
      ∑ a : CosetIndex Λ (n + 1) k,
        corankOneInverseTranslate abv π ℓ (labelledRep ϖ σ a) w := by
  simp only [corankOneMinusculeTranslate, LinearMap.sum_apply]

end Model

section Integrand

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {ψ : UnitaryAdditiveCharacter F} {n : ℕ}
variable (abv : AbsoluteValue F ℝ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
variable (ℓ : glFunctionals ψ (n + 1) π)
variable {ϖ : Fˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ)
variable (q : ℕ)
variable {Λ : Type uΛ} [Fintype Λ]

theorem corankOnePolynomialFunction_inverseTranslate
    (r g : Langlands.GeneralLinear (n + 1) F)
    (w : (coefficientModel π ℓ).toSubmodule) :
    corankOnePolynomialFunction ψ abv hϖ q
      (corankOneInverseTranslate abv π ℓ r w).val (g * r) =
      (w.val.val (rankInclusion 1 g) * determinantWeight abv g (0 - 1 / 2)) •
        sphericalWhittakerPolynomial hϖ (inverseStandardCharacter ψ n) q (g * r) := by
  simp only [corankOnePolynomialFunction, corankOneInverseTranslate_restriction,
    determinantWeight_mul]
  congr 1
  have hD := determinantWeight_ne_zero abv r (0 - 1 / 2)
  calc
    _ = ((determinantWeight abv r (0 - 1 / 2))⁻¹ *
      determinantWeight abv r (0 - 1 / 2)) *
        (w.val.val (rankInclusion 1 g) * determinantWeight abv g (0 - 1 / 2)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hD, one_mul]

theorem sphericalQuotientDegree_rightTranslate
    [IsTopologicalGroup (Langlands.GeneralLinear (n + 1) F)]
    (r : Langlands.GeneralLinear (n + 1) F) (a : LeftUnipotentQuotient n F) :
    sphericalQuotientDegree hϖ
      (rightTranslate (upperUnipotent (n + 1) F) r a) =
      sphericalQuotientDegree hϖ a + ∑ i, exponent hϖ r i := by
  induction a using Quotient.inductionOn with
  | h g =>
    simp only [rightTranslate_mk, sphericalQuotientDegree_mk, sum_exponent_mul]

variable (hψ : ∀ x ∈ (ValuativeRel.valuation F).integer, ψ x = 1)
variable (hq : 0 < q) (hcard : Fintype.card Λ = q)
variable (hgeneric : ∀ i : Fin n, ∃ x : F,
  (ValuativeRel.valuation F) x * (ValuativeRel.valuation F) (ϖ : F) ≤ 1 ∧
    inverseStandardCharacter ψ n (adjacentUnit i x) ≠ 1)
variable (σ : Λ → F)
variable (hσ : ∀ x, σ x ∈ (ValuativeRel.valuation F).integer)
variable (hinj : ∀ x y, (ValuativeRel.valuation F) (σ x - σ y) < 1 → x = y)
variable (hsurj : ∀ z ∈ (ValuativeRel.valuation F).integer,
  ∃ x, (ValuativeRel.valuation F) (z - σ x) < 1)

include hψ hq hcard hgeneric hσ hinj hsurj in
/-- The weighted inverse translates cancel their determinant weights before
the finite spherical eigenidentity is applied. -/
theorem sum_corankOnePolynomialFunction_inverseTranslate
    (k : ℕ) (w : (coefficientModel π ℓ).toSubmodule)
    (g : Langlands.GeneralLinear (n + 1) F) :
    (∑ a : CosetIndex Λ (n + 1) k,
      corankOnePolynomialFunction ψ abv hϖ q
        (corankOneInverseTranslate abv π ℓ (labelledRep ϖ σ a) w).val
          (g * labelledRep ϖ σ a)) =
      symmetricTorusHeckeScalar n q k *
        corankOnePolynomialFunction ψ abv hϖ q w.val g := by
  simp only [corankOnePolynomialFunction_inverseTranslate, ← Finset.smul_sum]
  change _ • sphericalWhittakerMinusculeSum hϖ (inverseStandardCharacter ψ n) q σ k g =
    symmetricTorusHeckeScalar n q k * _
  rw [sphericalWhittakerMinusculeSum_eq hϖ _ q hq hcard
    (isIntegrallyTrivial_inverseStandardCharacter hψ n) hgeneric σ hσ hinj hsurj]
  simp only [corankOnePolynomialFunction, Algebra.smul_def]
  ring

include hq hcard hgeneric hσ hinj hsurj in
theorem sum_corankOnePolynomialIntegrand_inverseTranslate
    [IsTopologicalGroup (Langlands.GeneralLinear (n + 1) F)]
    (k : ℕ) (w : (coefficientModel π ℓ).toSubmodule)
    (t : LeftUnipotentQuotient n F) :
    (∑ a : CosetIndex Λ (n + 1) k,
      corankOnePolynomialIntegrand ψ abv hϖ q
        (corankOneInverseTranslate abv π ℓ (labelledRep ϖ σ a) w).val hψ
          (rightTranslate (upperUnipotent (n + 1) F) (labelledRep ϖ σ a) t)) =
      symmetricTorusHeckeScalar n q k *
        corankOnePolynomialIntegrand ψ abv hϖ q w.val hψ t := by
  induction t using Quotient.inductionOn with
  | h g =>
    exact sum_corankOnePolynomialFunction_inverseTranslate abv π ℓ hϖ q hψ hq hcard
      hgeneric σ hσ hinj hsurj k w g

include hq hcard hgeneric hσ hinj hsurj in
/-- Every representative shifts the degree by the same integer `k`. -/
theorem sum_degreeCorankOnePolynomialIntegrand_inverseTranslate
    [IsTopologicalGroup (Langlands.GeneralLinear (n + 1) F)]
    (k : ℕ) (w : (coefficientModel π ℓ).toSubmodule)
    (d : ℤ) (t : LeftUnipotentQuotient n F) :
    (∑ a : CosetIndex Λ (n + 1) k,
      degreeCorankOnePolynomialIntegrand ψ abv hϖ q
        (corankOneInverseTranslate abv π ℓ (labelledRep ϖ σ a) w).val hψ d
          (rightTranslate (upperUnipotent (n + 1) F) (labelledRep ϖ σ a) t)) =
      symmetricTorusHeckeScalar n q k *
        degreeCorankOnePolynomialIntegrand ψ abv hϖ q w.val hψ (d - k) t := by
  classical
  simp only [degreeCorankOnePolynomialIntegrand, sphericalQuotientDegree_rightTranslate,
    sum_exponent_labelledRep]
  by_cases ht : sphericalQuotientDegree hϖ t = d - k
  · have ht' : sphericalQuotientDegree hϖ t + k = d := by omega
    simp only [ite_eq_left ht', ite_eq_left ht, sum_corankOnePolynomialIntegrand_inverseTranslate
      abv π ℓ hϖ q hψ hq hcard hgeneric σ hσ hinj hsurj]
  · have ht' : sphericalQuotientDegree hϖ t + k ≠ d := by omega
    simp only [ite_eq_right ht', ite_eq_right ht, Finset.sum_const_zero, mul_zero]

end Integrand

end Langlands.Conductor
