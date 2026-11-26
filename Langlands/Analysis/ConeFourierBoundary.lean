import Langlands.Analysis.ConeIntegralLimits
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Fourier boundary values for products of cone denominators -/

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

set_option autoImplicit false

namespace Langlands.Analysis

variable {ι : Type*} [Fintype ι]

private def orientedHalfLine (d : ℝ) : Set ℝ :=
  if 0 < d then Ioi 0 else Iio 0

/-- The open orthant oriented by the signs of `d`. -/
def orientedOrthant (d : ι → ℝ) : Set (ι → ℝ) :=
  univ.pi (fun i => orientedHalfLine (d i))

/-- The product of the orientation signs of the half-lines. -/
def orthantSign (d : ι → ℝ) : ℂ :=
  ∏ i, if 0 < d i then 1 else -1

private def shiftedParameter (d : ℝ) (t y : ℝ) : ℂ :=
  ((t * d : ℝ) : ℂ) + Complex.I * (y : ℂ)

/-- The product of the reciprocals of `t d_i + i y_i`. -/
def orthantReciprocal (d : ι → ℝ) (t : ℝ) (y : ι → ℝ) : ℂ :=
  ∏ i, (shiftedParameter (d i) t (y i))⁻¹

private def dot (x y : ι → ℝ) : ℝ := ∑ i, x i * y i

private def fourierKernel (x y : ι → ℝ) : ℂ :=
  Complex.exp (Complex.I * ((-dot x y : ℝ) : ℂ))

/-- The Fourier phase integrated against a spectral test using frequency measure `ν`. -/
def orthantFourierTest (ν : Measure (ι → ℝ)) (f : (ι → ℝ) → ℂ) (x : ι → ℝ) : ℂ :=
  ∫ y, fourierKernel x y * f y ∂ν

private theorem measurableSet_orientedOrthant (d : ι → ℝ) :
    MeasurableSet (orientedOrthant d) := by
  refine MeasurableSet.univ_pi fun i => ?_
  unfold orientedHalfLine
  split_ifs <;> simp

private theorem dot_nonneg_on_orientedOrthant (d : ι → ℝ)
    {x : ι → ℝ} (hx : x ∈ orientedOrthant d) : 0 ≤ dot d x := by
  apply Finset.sum_nonneg
  intro i _
  have hi : x i ∈ orientedHalfLine (d i) := hx i (mem_univ _)
  by_cases hp : 0 < d i
  · rw [orientedHalfLine, ite_eq_left hp] at hi
    exact mul_nonneg hp.le (le_of_lt (show 0 < x i from hi))
  · rw [orientedHalfLine, ite_eq_right hp] at hi
    exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hp) (le_of_lt (show x i < 0 from hi))

private theorem halfLine_laplace (d t y : ℝ) (ht : 0 < t) (hd : d ≠ 0) :
    let z := shiftedParameter d t y
    IntegrableOn (fun x : ℝ => Complex.exp (-z * x)) (orientedHalfLine d) ∧
      (∫ x : ℝ in orientedHalfLine d, Complex.exp (-z * x)) =
        (if 0 < d then 1 else -1) * z⁻¹ := by
  dsimp only
  have hz : (-(shiftedParameter d t y)).re = -(t * d) := by
    simp [shiftedParameter, Complex.mul_re]
  by_cases hp : 0 < d
  · rw [orientedHalfLine, ite_eq_left hp, ite_eq_left hp]
    have hn : (-(shiftedParameter d t y)).re < 0 := by
      rw [hz]
      exact neg_neg_of_pos (mul_pos ht hp)
    refine ⟨integrableOn_exp_mul_complex_Ioi hn 0, ?_⟩
    rw [integral_exp_mul_complex_Ioi hn]
    simp [div_eq_mul_inv]
  · rw [orientedHalfLine, ite_eq_right hp, ite_eq_right hp, ← integrableOn_Iic_iff_integrableOn_Iio,
      ← integral_Iic_eq_integral_Iio]
    have hn : 0 < (-(shiftedParameter d t y)).re := by
      rw [hz]
      exact neg_pos.mpr (mul_neg_of_pos_of_neg ht (lt_of_le_of_ne (le_of_not_gt hp) hd))
    refine ⟨integrableOn_exp_mul_complex_Iic hn 0, ?_⟩
    rw [integral_exp_mul_complex_Iic hn]
    simp [div_eq_mul_inv]

private theorem orthant_laplace (d : ι → ℝ) (t : ℝ) (y : ι → ℝ)
    (hd : ∀ i, d i ≠ 0) (ht : 0 < t) :
    let kernel (x : ι → ℝ) :=
      Complex.exp (∑ i, -(shiftedParameter (d i) t (y i)) * (x i : ℂ))
    IntegrableOn kernel (orientedOrthant d) ∧
      (∫ x in orientedOrthant d, kernel x) = orthantSign d * orthantReciprocal d t y := by
  dsimp only
  have hcoord (i : ι) := halfLine_laplace (d i) t (y i) ht (hd i)
  simp only [IntegrableOn, orientedOrthant, volume_pi, Measure.restrict_pi_pi, Complex.exp_sum]
  refine ⟨Integrable.fintype_prod (fun i => (hcoord i).1), ?_⟩
  rw [integral_fintype_prod_eq_prod
    (fun i (x : ℝ) => Complex.exp (-(shiftedParameter (d i) t (y i)) * x)),
    orthantSign, orthantReciprocal, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => (hcoord i).2

private theorem exp_shiftedParameter_sum (d : ι → ℝ) (t : ℝ) (x y : ι → ℝ) :
    Complex.exp (∑ i, -(shiftedParameter (d i) t (y i)) * (x i : ℂ)) =
      Real.exp (-(t * dot d x)) • fourierKernel x y := by
  rw [Complex.real_smul, Complex.ofReal_exp, fourierKernel, ← Complex.exp_add]
  congr 1
  simp only [shiftedParameter, dot]
  push_cast
  rw [← neg_mul, mul_neg, ← neg_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem norm_fourierKernel (x y : ι → ℝ) : ‖fourierKernel x y‖ = 1 := by
  exact Complex.norm_exp_I_mul_ofReal _

/-- Fubini identifies the product of shifted reciprocal parameters against an integrable
test with the Fourier test integrated over the exponentially damped orthant. -/
theorem orthantReciprocal_integral (d : ι → ℝ) (hd : ∀ i, d i ≠ 0)
    {ν : Measure (ι → ℝ)} [SFinite ν] {f : (ι → ℝ) → ℂ} (hf : Integrable f ν)
    {t : ℝ} (ht : 0 < t) :
    orthantSign d * (∫ y, orthantReciprocal d t y * f y ∂ν) =
      ∫ x in orientedOrthant d, Real.exp (-(t * dot d x)) • orthantFourierTest ν f x := by
  let μ : Measure (ι → ℝ) := volume.restrict (orientedOrthant d)
  let r (x : ι → ℝ) : ℝ := Real.exp (-(t * dot d x))
  have hr : Integrable r μ := by
    have h := (orthant_laplace d t 0 hd ht).1.norm
    simpa only [exp_shiftedParameter_sum, norm_smul, norm_fourierKernel, mul_one,
      Real.norm_of_nonneg (Real.exp_pos _).le] using h
  let g (x y : ι → ℝ) : ℂ := r x • (fourierKernel x y * f y)
  have hk : Continuous (fun p : (ι → ℝ) × (ι → ℝ) => fourierKernel p.1 p.2) := by
    unfold fourierKernel dot
    fun_prop
  have hrCont : Continuous r := by
    unfold r dot
    fun_prop
  have hg : Integrable (Function.uncurry g) (μ.prod ν) := by
    refine (hr.smul_prod hf).mono ?_ (ae_of_all _ fun p => ?_)
    · exact hrCont.aestronglyMeasurable.comp_fst.smul
        (hk.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd)
    · change ‖r p.1 • (fourierKernel p.1 p.2 * f p.2)‖ ≤ ‖r p.1 • f p.2‖
      simp only [norm_smul, norm_mul, norm_fourierKernel, one_mul, le_refl]
  calc
    _ = ∫ y, (∫ x, g x y ∂μ) ∂ν := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all ν fun y => by
        have hLaplace := (orthant_laplace d t y hd ht).2
        simp only [exp_shiftedParameter_sum] at hLaplace
        change orthantSign d * (orthantReciprocal d t y * f y) =
          ∫ x, r x • (fourierKernel x y * f y) ∂μ
        simp_rw [Complex.real_smul, ← mul_assoc]
        rw [integral_mul_const]
        exact congrArg (fun z : ℂ => z * f y) hLaplace.symm
    _ = ∫ x, (∫ y, g x y ∂ν) ∂μ := (integral_integral_swap hg).symm
    _ = _ := by
      simp_rw [g, integral_smul, orthantFourierTest]
      rfl

/-- Boundary value of the shifted reciprocal cone denominator evaluated on an integrable
spectral test whose Fourier integral is integrable on the cone. -/
def OrthantFourierBoundaryStatement : Prop :=
  ∀ {ι : Type*} [Fintype ι] (d : ι → ℝ) (ν : Measure (ι → ℝ)) [SFinite ν]
    (f : (ι → ℝ) → ℂ),
    (∀ i, d i ≠ 0) → Integrable f ν →
    IntegrableOn (orthantFourierTest ν f) (orientedOrthant d) →
    Tendsto (fun t : ℝ => orthantSign d * (∫ y, orthantReciprocal d t y * f y ∂ν))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x in orientedOrthant d, orthantFourierTest ν f x))

theorem orthantFourierBoundary : OrthantFourierBoundaryStatement := by
  intro ι _ d ν _ f hd hf hFourier
  let μ : Measure (ι → ℝ) := volume.restrict (orientedOrthant d)
  have hNonneg : ∀ᵐ x ∂μ, 0 ≤ dot d x :=
    (ae_restrict_mem (measurableSet_orientedOrthant d)).mono
      (fun _ hx => dot_nonneg_on_orientedOrthant d hx)
  have hMeas : Measurable (dot d) := by
    unfold dot
    fun_prop
  refine (tendsto_integral_remove_exponential_damping hMeas.aemeasurable hNonneg hFourier).congr' ?_
  filter_upwards [(self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)] with t ht
  exact (orthantReciprocal_integral d hd hf ht).symm

end Langlands.Analysis
