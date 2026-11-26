import Langlands.Global.RankinSelberg.ComplexTatePolynomialGaussian
import Langlands.Representation.GodementJacquet.ComplexMatrixHaar
import Mathlib.MeasureTheory.Integral.Pi

/-! # The circular Gaussian mean of a holomorphic polynomial -/

noncomputable section

open MeasureTheory MvPolynomial
open scoped SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.HolomorphicGaussianMean

open Langlands.GodementJacquet (complexAbsHom coe_complexAbsHom map_complex_mul_addHaar)
open Langlands.LocalFactor.ComplexTate (gaussian polynomialGaussian polynomialGaussian_apply)

local notation "scale" => (2 * Real.pi : ℝ)

private def scalarGaussian (z : ℂ) : ℂ := (Real.exp (-scale * ‖z‖ ^ 2) : ℂ)

private theorem scalarGaussian_eq (z : ℂ) : scalarGaussian z = (Real.pi : ℂ) * gaussian 0 z := by
  unfold scalarGaussian gaussian
  rw [ite_eq_left le_rfl, Int.natAbs_zero, pow_zero, one_mul, Complex.ofReal_exp]
  push_cast
  rw [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
  congr 1
  ring

private theorem integrable_scalarMonomial (μ : Measure ℂ) [μ.IsAddHaarMeasure] (k : ℕ) :
    Integrable (fun z : ℂ => z ^ k * scalarGaussian z) μ := by
  let F := polynomialGaussian ((X false : MvPolynomial Bool ℂ) ^ k)
  refine ((F.integrable (μ := μ)).const_mul (Real.pi : ℂ)).congr (ae_of_all _ fun z => ?_)
  change (Real.pi : ℂ) * polynomialGaussian ((X false : MvPolynomial Bool ℂ) ^ k) z =
    z ^ k * scalarGaussian z
  rw [scalarGaussian_eq, polynomialGaussian_apply, map_pow, eval_X, ite_eq_right (by decide : ¬false = true)]
  ring

private theorem integral_scalarMonomial_zero (μ : Measure ℂ) [μ.IsAddHaarMeasure]
    {k : ℕ} (hk : k ≠ 0) : (∫ z : ℂ, z ^ k * scalarGaussian z ∂μ) = 0 := by
  let a := Circle.exp (Real.pi / (k : ℝ))
  have ha : (a : ℂ) ^ k = -1 := by
    have hK : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    simp only [a, Circle.coe_exp, ← Complex.exp_nat_mul, Complex.ofReal_div, Complex.ofReal_natCast]
    rw [← mul_assoc, mul_div_cancel₀ _ hK, Complex.exp_pi_mul_I]
  let f (z : ℂ) := z ^ k * scalarGaussian z
  have hF : Continuous f := by unfold f scalarGaussian; fun_prop
  have hA : complexAbsHom (a : ℂ) = 1 := by
    apply NNReal.eq
    rw [coe_complexAbsHom, Circle.norm_coe]
    simp
  have hmap := map_complex_mul_addHaar μ (Circle.coe_ne_zero a)
  rw [hA, inv_one, one_smul] at hmap
  have hI : (∫ z, f ((a : ℂ) * z) ∂μ) = ∫ z, f z ∂μ := by
    have hm : Measurable fun z : ℂ => (a : ℂ) * z := (continuous_const.mul continuous_id).measurable
    nth_rw 2 [← hmap]
    exact (integral_map hm.aemeasurable hF.aestronglyMeasurable).symm
  have he (z : ℂ) : f ((a : ℂ) * z) = -f z := by
    simp only [f, scalarGaussian, norm_mul, Circle.norm_coe, one_mul, mul_pow, ha, neg_mul]
  simp only [he, integral_neg] at hI
  change (∫ z, f z ∂μ) = 0
  linear_combination -(1 / 2 : ℂ) * hI

private theorem scalarGaussian_integral_ne_zero (μ : Measure ℂ) [μ.IsAddHaarMeasure] :
    (∫ z, scalarGaussian z ∂μ) ≠ 0 := by
  let g (z : ℂ) := Real.exp (-scale * ‖z‖ ^ 2)
  have hg : Integrable g μ := by
    have h := (integrable_scalarMonomial μ 0).re
    change Integrable (fun z : ℂ => (z ^ (0 : ℕ) * scalarGaussian z).re) μ at h
    simpa only [pow_zero, one_mul, scalarGaussian, Complex.ofReal_re, g] using h
  have hpos : 0 < ∫ z, g z ∂μ := by
    apply (integral_pos_iff_support_of_nonneg (fun z => (Real.exp_pos _).le) hg).mpr
    rw [show Function.support g = Set.univ by ext z; simp [g, Function.mem_support, Real.exp_ne_zero]]
    exact (isOpen_univ : IsOpen (Set.univ : Set ℂ)).measure_pos μ Set.univ_nonempty
  change (∫ z : ℂ, (g z : ℂ) ∂μ) ≠ 0
  rw [integral_complex_ofReal]
  exact Complex.ofReal_ne_zero.mpr hpos.ne'

variable {ι : Type*} [Fintype ι]

/-- With product additive Haar measure on finitely many complex coordinates, the
Gaussian of scale `2π` has nonzero mass. The integral of any holomorphic polynomial
against it equals the mass times the value of the polynomial at the origin. -/
def HolomorphicGaussianMeanStatement : Prop :=
  ∀ (μ : Measure ℂ) [μ.IsAddHaarMeasure],
    let γ (z : ι → ℂ) := (Real.exp (-scale * ∑ i, ‖z i‖ ^ 2) : ℂ)
    let ν := Measure.pi (fun _ : ι => μ)
    (∫ z, γ z ∂ν) ≠ 0 ∧
      ∀ P : MvPolynomial ι ℂ,
        Integrable (fun z => eval z P * γ z) ν ∧
        (∫ z, eval z P * γ z ∂ν) = eval (fun _ => 0) P * ∫ z, γ z ∂ν

theorem holomorphicGaussianMean : HolomorphicGaussianMeanStatement (ι := ι) := by
  intro μ hμ γ ν
  classical
  have hγ (z : ι → ℂ) : γ z = ∏ i, scalarGaussian (z i) := by
    change (Real.exp (-scale * ∑ i, ‖z i‖ ^ 2) : ℂ) = _
    rw [Finset.mul_sum, Real.exp_sum, Complex.ofReal_prod]
    rfl
  constructor
  · simp only [hγ, ν, integral_fintype_prod_eq_prod, Finset.prod_const]
    exact pow_ne_zero _ (scalarGaussian_integral_ne_zero μ)
  intro P
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    have he (z : ι → ℂ) : eval z (monomial u a) * γ z =
        a * ∏ i, z i ^ u i * scalarGaussian (z i) := by
      rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), hγ, Finset.prod_mul_distrib]
      ring
    simp only [he]
    refine ⟨(Integrable.fintype_prod (fun i => integrable_scalarMonomial μ (u i))).const_mul a, ?_⟩
    by_cases hu : u = 0
    · subst u
      simp only [monomial_zero', eval_C, Finsupp.zero_apply, pow_zero, one_mul, ← hγ, integral_const_mul]
    · obtain ⟨j, hj⟩ : ∃ i, u i ≠ 0 := by
        by_contra! hz
        exact hu (Finsupp.ext hz)
      have hprod := integral_fintype_prod_eq_prod (μ := fun _ : ι => μ)
        (fun i z => z ^ u i * scalarGaussian z)
      rw [integral_const_mul, hprod,
        Finset.prod_eq_zero (Finset.mem_univ j) (integral_scalarMonomial_zero μ hj), mul_zero]
      rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
        Finset.prod_eq_zero (Finset.mem_univ j) (zero_pow hj), mul_zero, zero_mul]
  | add P Q hP hQ =>
    simp only [map_add, add_mul]
    exact ⟨hP.1.add hQ.1, by rw [integral_add hP.1 hQ.1, hP.2, hQ.2]⟩

end Langlands.Global.RankinSelbergGlobal.HolomorphicGaussianMean
