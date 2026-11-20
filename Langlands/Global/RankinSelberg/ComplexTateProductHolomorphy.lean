import Langlands.Global.RankinSelberg.ComplexTateProductConvergence
import Langlands.Global.RankinSelberg.UnequalAnalyticHolomorphy
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Holomorphy of the finite product Tate integral -/

noncomputable section

open Filter MeasureTheory Metric Set
open scoped SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexTateProduct

open UnequalAnalytic (abs_mul_exp_le aestronglyMeasurable_mul_cexp norm_mul_cexp)

private theorem differentiableAt_integral_mul_cexp_zero {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {A : X → ℂ} {L : X → ℝ} (hA : Integrable A μ)
    (hL : AEStronglyMeasurable L μ)
    (hplus : Integrable (fun x => ‖A x‖ * Real.exp (2 * L x)) μ)
    (hminus : Integrable (fun x => ‖A x‖ * Real.exp (-2 * L x)) μ) :
    DifferentiableAt ℂ (fun s : ℂ => ∫ x, A x * Complex.exp (s * L x) ∂μ) 0 := by
  let F' (s : ℂ) (x : X) := A x * (Complex.exp (s * L x) * L x)
  let bound (x : X) := ‖A x‖ * (Real.exp (2 * L x) + 2 + Real.exp (-2 * L x))
  have hm' : AEStronglyMeasurable (F' 0) μ := by
    convert hA.aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hL) using 1
    ext x
    simp [F', Pi.mul_apply]
  have hbound : Integrable bound μ := by
    refine ((hplus.add (hA.norm.const_mul 2)).add hminus).congr (.of_forall fun x => ?_)
    simp only [Pi.add_apply, bound]
    ring
  have hle : ∀ x, ∀ s ∈ ball (0 : ℂ) 1, ‖F' s x‖ ≤ bound x := by
    intro x s hs
    have hre : |s.re - 0| ≤ 1 := by
      rw [mem_ball_iff_norm, sub_zero] at hs
      simpa only [sub_zero] using (Complex.abs_re_le_norm s).trans hs.le
    have hb := abs_mul_exp_le (L x) hre
    simp only [zero_add, zero_sub, zero_mul, Real.exp_zero, mul_one] at hb
    simp only [F', bound, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    rw [show (s * (L x : ℂ)).re = s.re * L x by simp, mul_comm (Real.exp _)]
    exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
  have hderiv : ∀ x, ∀ s ∈ ball (0 : ℂ) 1,
      HasDerivAt (fun w : ℂ => A x * Complex.exp (w * L x)) (F' s x) s := by
    intro x s _
    simpa only [id, one_mul, F'] using HasDerivAt.const_mul (A x)
      (HasDerivAt.cexp (HasDerivAt.mul_const (hasDerivAt_id s) (L x : ℂ)))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds (0 : ℂ) one_pos)
    (Eventually.of_forall fun s => aestronglyMeasurable_mul_cexp hA.aestronglyMeasurable hL s)
    (by simpa using hA) hm' (Eventually.of_forall hle) hbound (Eventually.of_forall hderiv)).2.differentiableAt

variable {ι : Type*} [Fintype ι]

/-- The product Tate integral with additive Lebesgue measure on each complex coordinate. -/
def zeta (F : (ι → ℂ) → ℂ) (m : ι → ℤ) (u : ι → ℂ) : ℂ :=
  ∫ z, integrand F m u z

/-- Spectral parameters with real slopes in a single complex variable. -/
def affineParameter (t : ι → ℂ) (c : ι → ℝ) (s : ℂ) (j : ι) : ℂ :=
  t j + (c j : ℂ) * s

private def logSlope (c : ι → ℝ) (z : ι → ℂ) : ℝ :=
  ∑ j, 2 * c j * Real.log ‖z j‖

private theorem measurable_logSlope (c : ι → ℝ) : Measurable (logSlope c) :=
  Finset.measurable_sum _ fun j _ =>
    (Real.measurable_log.comp (continuous_norm.measurable.comp (measurable_pi_apply j))).const_mul _

omit [Fintype ι] in
private theorem additiveWeight_affine (m : ℤ) (t : ι → ℂ) (c : ι → ℝ) (s₀ s : ℂ)
    (j : ι) (z : ι → ℂ) :
    additiveWeight m (affineParameter t c s j) (z j) =
      additiveWeight m (affineParameter t c s₀ j) (z j) *
        Complex.exp ((s - s₀) * ((2 * c j * Real.log ‖z j‖ : ℝ) : ℂ)) := by
  by_cases hz : z j = 0
  · simp [additiveWeight, hz]
  simp only [additiveWeight, ite_eq_right hz]
  have hbase : (‖z j‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  rw [show 2 * affineParameter t c s j - 2 =
    (2 * affineParameter t c s₀ j - 2) + (s - s₀) * (2 * (c j : ℂ)) by
      unfold affineParameter
      ring,
    Complex.cpow_add _ _ hbase, ← mul_assoc]
  congr 1
  rw [Complex.cpow_def_of_ne_zero hbase, ← Complex.ofReal_log (norm_nonneg _)]
  congr 1
  push_cast
  ring

private theorem integrand_affine (F : (ι → ℂ) → ℂ) (m : ι → ℤ) (t : ι → ℂ) (c : ι → ℝ)
    (s₀ s : ℂ) (z : ι → ℂ) :
    integrand F m (affineParameter t c s) z = integrand F m (affineParameter t c s₀) z *
      Complex.exp ((s - s₀) * (logSlope c z : ℂ)) := by
  simp only [integrand, additiveWeight_affine (m _) t c s₀ s, Finset.prod_mul_distrib, mul_assoc]
  congr 1
  rw [logSlope, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  simp only [mul_assoc]

private theorem isOpen_positiveAffine (t : ι → ℂ) (c : ι → ℝ) :
    IsOpen {s : ℂ | ∀ j, 0 < (affineParameter t c s j).re} := by
  have hset : {s : ℂ | ∀ j, 0 < (affineParameter t c s j).re} =
      ⋂ j, {s : ℂ | 0 < (affineParameter t c s j).re} := by ext; simp
  rw [hset]
  exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const
    (Complex.continuous_re.comp (continuous_const.add (continuous_const.mul continuous_id)))

theorem differentiableOn_zeta_affine (F : 𝓢(ι → ℂ, ℂ)) (m : ι → ℤ)
    (t : ι → ℂ) (c : ι → ℝ) :
    DifferentiableOn ℂ (fun s => zeta F m (affineParameter t c s))
      {s : ℂ | ∀ j, 0 < (affineParameter t c s j).re} := by
  intro s₀ hs₀
  apply DifferentiableAt.differentiableWithinAt
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isOpen_positiveAffine t c) s₀ hs₀
  let δ := r / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let A := integrand F m (affineParameter t c s₀)
  let L := fun z => δ * logSlope c z
  let G := fun v : ℂ => ∫ z, A z * Complex.exp (v * L z)
  have hG (v : ℂ) : zeta F m (affineParameter t c (s₀ + (δ : ℂ) * v)) = G v := by
    apply integral_congr_ae
    filter_upwards with z
    rw [integrand_affine F m t c s₀]
    dsimp [G, A, L]
    congr 2
    push_cast
    ring
  have hA : Integrable A volume := integrable_integrand F m hs₀
  have hL : AEStronglyMeasurable L volume := ((measurable_logSlope c).const_mul δ).aestronglyMeasurable
  have hmoment (v : ℝ) (hv : |v| ≤ 2) : Integrable (fun z => ‖A z‖ * Real.exp (v * L z)) volume := by
    have hs : s₀ + (δ : ℂ) * (v : ℂ) ∈ ball s₀ r := by
      rw [mem_ball_iff_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hδ]
      have h := mul_le_mul_of_nonneg_left hv hδ.le
      dsimp [δ] at h ⊢
      linarith
    refine (integrable_integrand F m (hball hs)).norm.congr (.of_forall fun z => ?_)
    change ‖integrand F m (affineParameter t c (s₀ + (δ : ℂ) * (v : ℂ))) z‖ =
      ‖A z‖ * Real.exp (v * L z)
    rw [integrand_affine F m t c s₀, add_sub_cancel_left, norm_mul_cexp, Complex.re_ofReal_mul,
      Complex.ofReal_re]
    dsimp [L]
    congr 2
    ring
  have hdiff : DifferentiableAt ℂ G 0 := differentiableAt_integral_mul_cexp_zero hA hL
    (hmoment 2 (by norm_num)) (hmoment (-2) (by norm_num))
  let v := fun s : ℂ => (s - s₀) / (δ : ℂ)
  have hv : v s₀ = 0 := by simp [v]
  have hvd : DifferentiableAt ℂ v s₀ := (differentiableAt_id.sub_const _).div_const _
  have hcomp := (show DifferentiableAt ℂ G (v s₀) from hv ▸ hdiff).comp s₀ hvd
  have hFun : G ∘ v = fun s => zeta F m (affineParameter t c s) := by
    funext s
    rw [Function.comp_apply, ← hG, show s₀ + (δ : ℂ) * v s = s by
      have hδ' : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ.ne'
      dsimp [v]
      field_simp
      ring]
  rwa [hFun] at hcomp

/-- Holomorphy on the open set where all coordinate real parts are positive. -/
def ComplexTateProductHolomorphyStatement : Prop :=
  ∀ (n : ℕ) (F : 𝓢(Fin n → ℂ, ℂ)) (m : Fin n → ℤ) (t : Fin n → ℂ) (c : Fin n → ℝ),
    AnalyticOnNhd ℂ (fun s => zeta F m (affineParameter t c s))
      {s : ℂ | ∀ j, 0 < (affineParameter t c s j).re}

theorem complexTateProductHolomorphy : ComplexTateProductHolomorphyStatement :=
  fun _ F m t c => (differentiableOn_zeta_affine F m t c).analyticOnNhd (isOpen_positiveAffine t c)

end Langlands.Global.RankinSelbergGlobal.ComplexTateProduct
