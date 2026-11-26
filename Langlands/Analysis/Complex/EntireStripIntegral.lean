import Langlands.Analysis.Complex.EntireStripExtension
import Langlands.Analysis.DominatedHolomorphicIntegral

/-! # Integrating entire families controlled on vertical lines -/

noncomputable section

open Filter MeasureTheory Metric Set
open scoped Topology

set_option autoImplicit false

namespace Langlands.Analysis

open Langlands.LocalFactor.Archimedean (HasStripExponentialGrowth)

variable {X : Type*} [MeasurableSpace X]

/-- A parameter family of entire functions is measurable at every argument if it is measurable
at each argument on one right half-plane. -/
theorem measurable_entireFamily_of_right {F : X → ℂ → ℂ} (hF : ∀ x, Differentiable ℂ (F x))
    {b : ℝ} (hM : ∀ s : ℂ, b < s.re → Measurable (fun x => F x s)) (s : ℂ) :
    Measurable (fun x => F x s) := by
  let c : ℂ := ((b + 2 : ℝ) : ℂ)
  have hc (θ : ℝ) : b < (circleMap c 1 θ).re := by
    have hb : ‖circleMap c 1 θ - c‖ = 1 := by
      rw [← dist_eq_norm, ← mem_sphere]
      exact circleMap_mem_sphere c zero_le_one θ
    have h := Complex.abs_re_le_norm (circleMap c 1 θ - c)
    rw [hb, Complex.sub_re, show c.re = b + 2 from Complex.ofReal_re _] at h
    linarith [neg_le_abs ((circleMap c 1 θ).re - (b + 2))]
  have hm : Measurable (fun p : ℝ × X => F p.2 (circleMap c 1 p.1)) :=
    measurable_uncurry_of_continuous_of_measurable (u := fun θ x => F x (circleMap c 1 θ))
      (fun x => (hF x).continuous.comp (continuous_circleMap c 1)) (fun θ => hM _ (hc θ))
  have hCoeff (j : ℕ) : Measurable (fun x => cauchyPowerSeries (F x) c 1 j (fun _ => s - c)) := by
    let K (p : X × ℝ) := deriv (circleMap c 1) p.2 •
      (((s - c) / (circleMap c 1 p.2 - c)) ^ j •
        (circleMap c 1 p.2 - c)⁻¹ • F p.1 (circleMap c 1 p.2))
    have hK : Measurable K := by
      refine ((measurable_deriv (circleMap c 1)).comp measurable_snd).smul ?_
      have h := ((continuous_circleMap c 1).measurable.comp (measurable_snd : Measurable (Prod.snd : X × ℝ → ℝ))).sub_const c
      exact ((measurable_const.div h).pow_const _).smul (h.inv.smul (hm.comp measurable_swap))
    have hI := (hK.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 (2 * Real.pi)))).measurable
    simp_rw [cauchyPowerSeries_apply, circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le]
    exact hI.const_smul ((2 * Real.pi * Complex.I : ℂ)⁻¹)
  have hSum (x : X) : HasSum (fun j => cauchyPowerSeries (F x) c 1 j (fun _ => s - c)) (F x s) := by
    have h := (hF x).hasFPowerSeriesOnBall c (R := 1) zero_lt_one
    simpa only [add_sub_cancel, NNReal.coe_one] using h.hasSum (y := s - c) (by simp)
  have he : (fun x => F x s) = fun x => ∑' j, cauchyPowerSeries (F x) c 1 j (fun _ => s - c) :=
    funext fun x => (hSum x).tsum_eq.symm
  rw [he]
  exact Measurable.tsum hCoeff

/-- Entire fibers with exponential strip growth integrate to an entire function if each
bounded real interval lies strictly between two vertical lines with a common integrable
exponential bound. -/
def EntireStripIntegralStatement : Prop :=
  ∀ (μ : Measure X) (F : X → ℂ → ℂ),
    (∀ s, AEStronglyMeasurable (fun x => F x s) μ) →
    (∀ᵐ x ∂μ, Differentiable ℂ (F x) ∧ HasStripExponentialGrowth (F x)) →
    (∀ u v : ℝ, u ≤ v → ∃ a b K : ℝ, a < u ∧ v < b ∧
      ∃ B : X → ℝ, Integrable B μ ∧
        ∀ᵐ x ∂μ, 0 ≤ B x ∧ ∀ s : ℂ, s.re = a ∨ s.re = b →
          ‖F x s‖ ≤ B x * Real.exp (K * |s.im|)) →
    (∀ s, Integrable (fun x => F x s) μ) ∧ Differentiable ℂ (fun s => ∫ x, F x s ∂μ)

theorem entireStripIntegral : EntireStripIntegralStatement (X := X) := by
  intro μ F hM hF hLine
  obtain ⟨hi, hd⟩ := dominatedHolomorphicIntegral (E := ℂ) μ univ (fun s x => F x s) hM
    (hF.mono fun x hx => hx.1.differentiableOn) (by
      intro z _
      let u := z.re - 1
      let v := z.re + 1
      obtain ⟨a, b, K, ha, hb, B, hB, hLineB⟩ := hLine u v (by dsimp [u, v]; linarith)
      have hab : a < b := by dsimp [u, v] at ha hb; linarith
      let C := Real.exp ((max |a| |b|) ^ 2 + K ^ 2 / 4 + (1 + K ^ 2 / 4) * (|z.im| + 1))
      refine ⟨1 / 2, by norm_num, subset_univ _, fun x => B x * C, hB.mul_const _, ?_⟩
      filter_upwards [hF, hLineB] with x hx hxB w hw
      have hDist : ‖w - z‖ < 1 := by
        rw [mem_ball, dist_eq_norm] at hw
        norm_num at hw ⊢
        exact hw
      have hre := (Complex.abs_re_le_norm (w - z)).trans hDist.le
      have him := (Complex.abs_im_le_norm (w - z)).trans hDist.le
      rw [Complex.sub_re] at hre
      rw [Complex.sub_im] at him
      have hwa : a ≤ w.re := by dsimp [u] at ha; linarith [(abs_le.mp hre).1]
      have hwb : w.re ≤ b := by dsimp [v] at hb; linarith [(abs_le.mp hre).2]
      have hwim : |w.im| ≤ |z.im| + 1 := by
        calc
          _ = |(w.im - z.im) + z.im| := by rw [sub_add_cancel]
          _ ≤ _ := (abs_add_le _ _).trans (by linarith)
      refine (norm_le_of_exp_bounds_on_vertical_lines hx.1 hx.2 hab hxB.1 hxB.2 hwa hwb).trans ?_
      dsimp only [C]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by gcongr)) hxB.1)
  exact ⟨fun s => hi s (mem_univ s), differentiableOn_univ.mp hd⟩

end Langlands.Analysis
