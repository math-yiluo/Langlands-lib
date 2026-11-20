import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Prod

/-! # Sub-mean-value inequalities for `log⁺ ‖g‖`

For a holomorphic function `g`, the function `log⁺ ‖g‖` lies below its averages:

* `posLog_norm_le_circleAverage`: over circles, for `g : ℂ → ℂ` analytic on a closed disc
  (from Jensen's formula);
* `measureReal_ball_mul_posLog_norm_le`: over balls, for `g : E → ℂ` holomorphic near a closed
  ball of a finite-dimensional complex normed space `E` and any additive Haar measure on `E`.

The ball version averages the circle version over the complex lines through the centre; it uses
that multiplication by a complex number of modulus one preserves every additive Haar measure
(`map_smul_addHaar_of_norm_eq_one`). -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.SeveralComplex

open Metric Set Filter MeasureTheory Real
open scoped Topology

/-- **Circle sub-mean-value inequality** for `log⁺ ‖g‖`, `g` analytic on a closed disc. -/
theorem posLog_norm_le_circleAverage {g : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall c R)) :
    posLog ‖g c‖ ≤ circleAverage (fun z => posLog ‖g z‖) c R := by
  have hRabs : |R| = R := abs_of_pos hR
  have hint : CircleIntegrable (fun z => posLog ‖g z‖) c R := by
    apply ContinuousOn.circleIntegrable'
    rw [hRabs]
    exact continuous_posLog.comp_continuousOn
      (continuous_norm.comp_continuousOn (hg.continuousOn.mono sphere_subset_closedBall))
  have h0 : 0 ≤ circleAverage (fun z => posLog ‖g z‖) c R :=
    circleAverage_nonneg_of_nonneg fun x _ => posLog_nonneg
  rw [posLog_apply]
  refine max_le h0 ?_
  by_cases hgc : g c = 0
  · simpa [hgc] using h0
  have hg' : AnalyticOnNhd ℂ g (closedBall c |R|) := by rwa [hRabs]
  have hlogint : CircleIntegrable (fun z => Real.log ‖g z‖) c R :=
    (hg'.meromorphicOn.mono_set sphere_subset_closedBall).circleIntegrable_log_norm
  have hJ := AnalyticOnNhd.circleAverage_log_norm hR.ne' hg' hgc
  have hsum : 0 ≤ ∑ᶠ u, (MeromorphicOn.divisor g (closedBall c |R|) u : ℝ) *
      Real.log (R * ‖c - u‖⁻¹) := by
    refine finsum_nonneg fun u => ?_
    by_cases h1 : u ∈ closedBall c |R|
    · refine mul_nonneg (mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hg' u) ?_
      by_cases hcu : u = c
      · simp [hcu]
      · have hpos : 0 < ‖c - u‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hcu))
        have hle : ‖c - u‖ ≤ R := by
          rw [mem_closedBall, dist_eq_norm', hRabs] at h1
          exact h1
        apply Real.log_nonneg
        rw [← div_eq_mul_inv, le_div_iff₀ hpos, one_mul]
        exact hle
    · simp [h1]
  calc Real.log ‖g c‖ ≤ circleAverage (fun z => Real.log ‖g z‖) c R := by
        rw [hJ]; linarith
    _ ≤ circleAverage (fun z => posLog ‖g z‖) c R :=
        circleAverage_mono hlogint hint fun x _ => le_max_right _ _

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Multiplication by a complex number of modulus one preserves every additive Haar measure on a
finite-dimensional complex normed space. -/
theorem measurePreserving_smul_of_norm_eq_one {a : ℂ} (ha : ‖a‖ = 1) :
    MeasurePreserving (fun x : E => a • x) μ μ := by
  have ha0 : a ≠ 0 := by
    intro h; rw [h, norm_zero] at ha; exact zero_ne_one ha
  set f : E ≃ₗ[ℝ] E := (LinearEquiv.smulOfNeZero ℂ E a ha0).restrictScalars ℝ with hf
  have hdet : LinearMap.det (f : E →ₗ[ℝ] E) ≠ 0 := (LinearEquiv.isUnit_det' f).ne_zero
  have hcont : Continuous fun x : E => a • x := continuous_const_smul a
  refine ⟨hcont.measurable, ?_⟩
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet
  have hcoe : ((f : E →ₗ[ℝ] E) : E → E) = fun x => a • x := rfl
  rw [hcoe] at hmap
  rw [hmap]
  -- the scaling constant is `1`, as one sees on the unit ball
  have hball := Measure.addHaar_preimage_linearMap μ hdet (ball (0 : E) 1)
  rw [hcoe] at hball
  have hpre : (fun x : E => a • x) ⁻¹' ball 0 1 = ball 0 1 := by
    ext x; simp [norm_smul, ha]
  rw [hpre] at hball
  have hpos : μ (ball (0 : E) 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have htop : μ (ball (0 : E) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have h1 : ENNReal.ofReal |(LinearMap.det (f : E →ₗ[ℝ] E))⁻¹| = 1 := by
    have := hball.symm
    rw [← one_mul (μ (ball (0 : E) 1))] at this
    conv_rhs at this => rw [one_mul]
    exact (ENNReal.mul_left_inj hpos htop).1 (by simpa using this)
  rw [h1, one_smul]

/-- Rotation invariance of integrals over centred balls. -/
theorem setIntegral_ball_smul_of_norm_eq_one {a : ℂ} (ha : ‖a‖ = 1) (h : E → ℝ) (r : ℝ) :
    ∫ x in ball (0 : E) r, h (a • x) ∂μ = ∫ x in ball (0 : E) r, h x ∂μ := by
  have ha0 : a ≠ 0 := by
    intro h; rw [h, norm_zero] at ha; exact zero_ne_one ha
  have hemb : MeasurableEmbedding fun x : E => a • x :=
    (Homeomorph.smulOfNeZero a ha0).measurableEmbedding
  have := (measurePreserving_smul_of_norm_eq_one μ ha).setIntegral_preimage_emb hemb h
    (ball 0 r)
  have hpre : (fun x : E => a • x) ⁻¹' ball 0 r = ball 0 r := by
    ext x; simp [norm_smul, ha]
  rwa [hpre] at this

omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] in
/-- Translation of integrals over balls. -/
theorem setIntegral_ball_add (h : E → ℝ) (z : E) (r : ℝ) :
    ∫ x in ball (0 : E) r, h (z + x) ∂μ = ∫ x in ball z r, h x ∂μ := by
  have := (measurePreserving_add_left μ z).setIntegral_preimage_emb
    (measurableEmbedding_addLeft z) h (ball z r)
  have hpre : (fun x : E => z + x) ⁻¹' ball z r = ball 0 r := by
    ext x; simp
  rwa [hpre] at this

/-- **Ball sub-mean-value inequality** for `log⁺ ‖g‖`, with `g` holomorphic on an open set
containing the closed ball. -/
theorem measureReal_ball_mul_posLog_norm_le {g : E → ℂ} {U : Set E} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) {z : E} {r : ℝ} (hr : 0 < r) (hsub : closedBall z r ⊆ U) :
    μ.real (ball z r) * posLog ‖g z‖ ≤ ∫ x in ball z r, posLog ‖g x‖ ∂μ := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  set u : E → ℝ := fun x => posLog ‖g x‖ with hu_def
  have hu : ContinuousOn u U :=
    continuous_posLog.comp_continuousOn (continuous_norm.comp_continuousOn hg.continuousOn)
  -- the integrand on `ball 0 r × (0, 2π]`
  set F : E × ℝ → ℝ := fun p => u (z + circleMap 0 1 p.2 • p.1) with hF_def
  have hmaps : ∀ x ∈ closedBall (0 : E) r, ∀ θ : ℝ, z + circleMap 0 1 θ • x ∈ U := by
    intro x hx θ
    apply hsub
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_circleMap_zero,
      abs_one, one_mul]
    simpa using hx
  have hFc : ContinuousOn F (closedBall (0 : E) r ×ˢ Icc 0 (2 * π)) := by
    refine hu.comp (by fun_prop) ?_
    intro p hp
    exact hmaps p.1 hp.1 p.2
  have hFint : Integrable F ((μ.restrict (ball 0 r)).prod (volume.restrict (Ioc 0 (2 * π)))) := by
    rw [Measure.prod_restrict]
    exact (hFc.integrableOn_compact ((isCompact_closedBall _ _).prod isCompact_Icc)).mono_set
      (prod_mono ball_subset_closedBall Ioc_subset_Icc_self)
  -- pointwise circle sub-mean inequality along complex lines
  have hcirc : ∀ x ∈ ball (0 : E) r,
      u z ≤ (2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), F (x, θ) := by
    intro x hx
    set W : Set ℂ := {ζ | z + ζ • x ∈ U} with hW
    have hWo : IsOpen W := hU.preimage (by fun_prop)
    have hWd : DifferentiableOn ℂ (fun ζ : ℂ => g (z + ζ • x)) W := by
      intro ζ hζ
      exact ((hg _ hζ).comp ζ
        ((differentiableAt_id.smul_const x).const_add z).differentiableWithinAt
        (fun ζ' hζ' => hζ'))
    have hWb : closedBall (0 : ℂ) 1 ⊆ W := by
      intro ζ hζ
      apply hsub
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
      rw [mem_closedBall, dist_zero_right] at hζ
      rw [mem_ball, dist_zero_right] at hx
      nlinarith [norm_nonneg ζ, norm_nonneg x]
    have h := posLog_norm_le_circleAverage one_pos ((hWd.analyticOnNhd hWo).mono hWb)
    simp only [zero_smul, add_zero] at h
    rw [circleAverage_def, intervalIntegral.integral_of_le (by positivity), smul_eq_mul] at h
    exact h
  have hleft : ∫ x in ball (0 : E) r, u z ∂μ ≤
      ∫ x in ball (0 : E) r, (2 * π)⁻¹ * (∫ θ in Ioc 0 (2 * π), F (x, θ)) ∂μ := by
    refine setIntegral_mono_on ?_ ?_ measurableSet_ball hcirc
    · exact integrableOn_const measure_ball_lt_top.ne
    · exact hFint.integral_prod_left.const_mul _
  rw [integral_const_mul, integral_integral_swap (f := fun x θ => F (x, θ)) hFint] at hleft
  -- each rotated copy of the ball integral equals the integral over `ball z r`
  have hθ : ∀ θ : ℝ, ∫ x in ball (0 : E) r, F (x, θ) ∂μ = ∫ x in ball z r, u x ∂μ := by
    intro θ
    rw [← setIntegral_ball_add μ u z r]
    have h1 : ‖circleMap 0 1 θ‖ = 1 := by rw [norm_circleMap_zero, abs_one]
    exact setIntegral_ball_smul_of_norm_eq_one μ h1 (fun y => u (z + y)) r
  simp only [hθ] at hleft
  rw [setIntegral_const, setIntegral_const, Real.volume_real_Ioc_of_le (by positivity),
    smul_eq_mul, smul_eq_mul, sub_zero] at hleft
  have hπ : (2 * π)⁻¹ * (2 * π * ∫ x in ball z r, u x ∂μ) = ∫ x in ball z r, u x ∂μ := by
    field_simp
  rw [hπ, ← Measure.addHaar_real_ball_center μ z r] at hleft
  exact hleft

end Langlands.Analysis.SeveralComplex
