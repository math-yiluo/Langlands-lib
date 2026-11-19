import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! # Complex Tate zeta integrals

Absolute convergence and holomorphy on the positive half-plane for the angular zeta
integrals of complex Schwartz functions. The spectral variable here absorbs the quasicharacter
parameter. The measure is twice area.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped SchwartzMap Topology ENNReal

namespace Langlands.LocalFactor.ComplexTate

/-- The self-dual area normalization for the basic trace character. -/
def measure : Measure ℂ := (2 : ℝ≥0∞) • volume

/-- The unit direction of a nonzero complex number, extended by zero. -/
def direction (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

theorem direction_mul (x z : ℂ) : direction (x * z) = direction x * direction z := by
  simp only [direction, norm_mul, ofReal_mul, mul_div_mul_comm]

theorem direction_ne_zero {z : ℂ} (hz : z ≠ 0) : direction z ≠ 0 :=
  div_ne_zero hz (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))

theorem norm_direction {z : ℂ} (hz : z ≠ 0) : ‖direction z‖ = 1 := by
  rw [direction, norm_div, Complex.norm_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr hz)]

/-- The complex zeta integrand, with the single point zero assigned value zero. -/
def integrand (f : ℂ → ℂ) (m : ℤ) (u : ℂ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else f z * direction z ^ m * (‖z‖ : ℂ) ^ (2 * u - 2)

/-- The zeta integral in the spectral variable `u = s + t`. -/
def zeta (f : ℂ → ℂ) (m : ℤ) (u : ℂ) : ℂ := ∫ z, integrand f m u z ∂measure

theorem measurable_integrand {f : ℂ → ℂ} (hf : Measurable f) (m : ℤ) (u : ℂ) :
    Measurable (integrand f m u) := by
  unfold integrand direction
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  fun_prop

theorem norm_integrand {z : ℂ} (hz : z ≠ 0) (f : ℂ → ℂ) (m : ℤ) (u : ℂ) :
    ‖integrand f m u z‖ = ‖f z‖ * ‖z‖ ^ (2 * u.re - 2) := by
  simp [integrand, hz, norm_zpow, norm_direction hz,
    norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr hz), mul_re, sub_re]

theorem zeta_const_mul (b : ℂ) (f : ℂ → ℂ) (m : ℤ) (u : ℂ) :
    zeta (fun z => b * f z) m u = b * zeta f m u := by
  have h (z : ℂ) : integrand (fun w => b * f w) m u z = b * integrand f m u z := by
    unfold integrand
    split_ifs <;> ring
  simp only [zeta, h, integral_const_mul]

theorem integrable_integrand_volume (f : 𝓢(ℂ, ℂ)) (m : ℤ) {u : ℂ} (hu : 0 < u.re) :
    Integrable (integrand f m u) volume := by
  have hm := measurable_integrand f.continuous.measurable m u
  have hball : IntegrableOn (integrand f m u) (Metric.ball 0 1) volume := by
    refine integrableOn_ball_of_norm_le_rpow (C := SchwartzMap.seminorm ℝ 0 0 f)
      (α := -(2 * u.re - 2)) (by simp [finrank_real_complex])
      (by rw [finrank_real_complex]; push_cast; linarith) ?_ hm.aestronglyMeasurable
    refine ae_restrict_of_ae ?_
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with z hz
    rw [norm_integrand hz, neg_neg]
    exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℝ f z)
      (Real.rpow_nonneg (norm_nonneg _) _)
  obtain ⟨k, hk⟩ := exists_nat_ge (2 * u.re - 2)
  have htail : IntegrableOn (integrand f m u) (Metric.ball 0 1)ᶜ volume := by
    refine ((f.integrable_pow_mul volume k).integrableOn).mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet.compl] with z hz
    have hz' : 1 ≤ ‖z‖ := by simpa [Metric.mem_ball, dist_zero_right] using hz
    have hne : z ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le hz')
    rw [norm_integrand hne, mul_comm, ← Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hz' hk) (norm_nonneg _)
  simpa using hball.union htail

theorem integrable_integrand (f : 𝓢(ℂ, ℂ)) (m : ℤ) {u : ℂ} (hu : 0 < u.re) :
    Integrable (integrand f m u) measure :=
  (integrable_integrand_volume f m hu).smul_measure (by simp)

private lemma rpow_mul_abs_log_le {r δ e lo hi : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hlo : lo ≤ e - δ) (hhi : e + δ ≤ hi) :
    r ^ e * |Real.log r| ≤ (r ^ hi + r ^ lo) / δ := by
  rcases le_or_gt 1 r with hr' | hr'
  · rw [abs_of_nonneg (Real.log_nonneg hr')]
    calc
      _ ≤ r ^ e * (r ^ δ / δ) :=
        mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hr.le hδ) (by positivity)
      _ = r ^ (e + δ) / δ := by rw [← mul_div_assoc, ← Real.rpow_add hr]
      _ ≤ _ := div_le_div_of_nonneg_right
        (le_add_of_le_of_nonneg (Real.rpow_le_rpow_of_exponent_le hr' hhi) (by positivity)) hδ.le
  · rw [abs_of_neg (Real.log_neg hr hr')]
    have hlog := Real.log_le_rpow_div (inv_nonneg.mpr hr.le) hδ
    rw [Real.log_inv, ← Real.rpow_neg_eq_inv_rpow] at hlog
    calc
      _ ≤ r ^ e * (r ^ (-δ) / δ) := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = r ^ (e - δ) / δ := by rw [← mul_div_assoc, ← Real.rpow_add hr, sub_eq_add_neg]
      _ ≤ _ := div_le_div_of_nonneg_right
        (le_add_of_nonneg_of_le (by positivity)
          (Real.rpow_le_rpow_of_exponent_ge hr hr'.le hlo)) hδ.le

theorem differentiableAt_zeta (f : 𝓢(ℂ, ℂ)) (m : ℤ) {u : ℂ} (hu : 0 < u.re) :
    DifferentiableAt ℂ (zeta f m) u := by
  let δ := u.re / 2
  have hδ : 0 < δ := half_pos hu
  let derivative (v z : ℂ) := integrand f m v z * ((Real.log ‖z‖ : ℂ) * 2)
  let bound (z : ℂ) :=
    (2 / δ) * (‖integrand f m (u + (δ : ℂ)) z‖ + ‖integrand f m (u - (δ : ℂ)) z‖)
  have hplus : 0 < (u + (δ : ℂ)).re := by
    rw [add_re, ofReal_re]
    positivity
  have hminus : 0 < (u - (δ : ℂ)).re := by
    rw [sub_re, ofReal_re]
    dsimp [δ]
    linarith
  have hbound : Integrable bound measure :=
    ((integrable_integrand f m hplus).norm.add
      (integrable_integrand f m hminus).norm).const_mul _
  have hmeas (v : ℂ) := measurable_integrand f.continuous.measurable m v
  have hmeas' : Measurable (derivative u) :=
    (hmeas u).mul ((continuous_ofReal.measurable.comp
      (Real.measurable_log.comp continuous_norm.measurable)).mul_const 2)
  have hle (z v : ℂ) (hv : v ∈ Metric.ball u (δ / 2)) : ‖derivative v z‖ ≤ bound z := by
    by_cases hz : z = 0
    · simp [hz, derivative, bound, integrand]
    have hv' : |v.re - u.re| < δ / 2 := by
      rw [Metric.mem_ball, dist_eq_norm] at hv
      simpa only [sub_re] using (abs_re_le_norm (v - u)).trans_lt hv
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hv'
    have h := rpow_mul_abs_log_le (norm_pos_iff.mpr hz) hδ
      (e := 2 * v.re - 2) (lo := 2 * (u.re - δ) - 2) (hi := 2 * (u.re + δ) - 2)
      (by linarith) (by linarith)
    simp only [derivative, bound, norm_mul, norm_real, Real.norm_eq_abs, Complex.norm_two,
      norm_integrand hz, add_re, sub_re, ofReal_re]
    calc
      _ = (2 * ‖f z‖) * (‖z‖ ^ (2 * v.re - 2) * |Real.log ‖z‖|) := by ring
      _ ≤ (2 * ‖f z‖) *
          ((‖z‖ ^ (2 * (u.re + δ) - 2) + ‖z‖ ^ (2 * (u.re - δ) - 2)) / δ) :=
        mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by ring
  have hdiff (z v : ℂ) : HasDerivAt (fun w => integrand f m w z) (derivative v z) v := by
    by_cases hz : z = 0
    · simpa [hz, integrand, derivative] using hasDerivAt_const v (0 : ℂ)
    have hn : (‖z‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    have hp := (((hasDerivAt_id' v).const_mul (2 : ℂ)).sub_const 2).const_cpow (Or.inl hn)
    simpa [integrand, derivative, hz, ofReal_log (norm_nonneg z), mul_assoc] using
      hp.const_mul (f z * direction z ^ m)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds u (half_pos hδ))
    (Eventually.of_forall fun v => (hmeas v).aestronglyMeasurable)
    (integrable_integrand f m hu) hmeas'.aestronglyMeasurable
    (Eventually.of_forall hle) hbound
    (Eventually.of_forall fun z v _ => hdiff z v)).2.differentiableAt

theorem analyticAt_zeta (f : 𝓢(ℂ, ℂ)) (m : ℤ) {u : ℂ} (hu : 0 < u.re) :
    AnalyticAt ℂ (zeta f m) u := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
  have hdiff : DifferentiableOn ℂ (zeta f m) {w : ℂ | 0 < w.re} :=
    fun _ hw => (differentiableAt_zeta f m hw).differentiableWithinAt
  exact hdiff.analyticAt (hopen.mem_nhds hu)

end Langlands.LocalFactor.ComplexTate
