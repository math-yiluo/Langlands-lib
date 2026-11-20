import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Cauchy estimates and holomorphic parametric integrals

For a complex normed space `E` and a complex normed space `F`:

* `norm_fderiv_le_of_forall_norm_le`: the Cauchy estimate `‖Df(x)‖ ≤ M / r'` for a function
  holomorphic on the ball of radius `r > r'` around `x` and bounded by `M` there;
* `differentiableOn_intervalIntegral_of_continuousOn`: an interval integral of a jointly
  continuous integrand that is holomorphic in the parameter is holomorphic in the parameter;
* `differentiableOn_circleIntegral_of_continuousOn`: the same for circle integrals. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.SeveralComplex

open Metric Set Filter MeasureTheory
open scoped Topology Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **Cauchy estimate** for the derivative of a holomorphic function of several variables:
if `f` is holomorphic on `ball x r` and bounded by `M` there, then `‖Df(x)‖ ≤ M / r'` for
every `0 < r' < r`. -/
theorem norm_fderiv_le_of_forall_norm_le {f : E → F} {x : E} {r r' M : ℝ} (hr' : 0 < r')
    (hrr' : r' < r) (hd : DifferentiableOn ℂ f (ball x r))
    (hM : ∀ y ∈ ball x r, ‖f y‖ ≤ M) : ‖fderiv ℂ f x‖ ≤ M / r' := by
  have hr : 0 < r := hr'.trans hrr'
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x (mem_ball_self hr))
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hM0 hr'.le) fun u => ?_
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hu' : 0 < ‖u‖ := norm_pos_iff.2 hu
  set R : ℝ := r' / ‖u‖ with hRdef
  have hR : 0 < R := div_pos hr' hu'
  set g : ℂ → F := fun t => f (x + t • u) with hgdef
  have hmem : ∀ t : ℂ, ‖t‖ ≤ R → x + t • u ∈ ball x r := by
    intro t ht
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    calc ‖t‖ * ‖u‖ ≤ R * ‖u‖ := by gcongr
      _ = r' := by rw [hRdef]; field_simp
      _ < r := hrr'
  have hgd : ∀ t : ℂ, ‖t‖ ≤ R → DifferentiableAt ℂ g t := by
    intro t ht
    have hfx : DifferentiableAt ℂ f (x + t • u) :=
      (hd _ (hmem t ht)).differentiableAt (isOpen_ball.mem_nhds (hmem t ht))
    exact hfx.comp t ((differentiableAt_id.smul_const u).const_add x)
  have hdc : DiffContOnCl ℂ g (ball (0 : ℂ) R) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ hR.ne']
    intro t ht
    exact (hgd t (by simpa using ht)).differentiableWithinAt
  have hbound : ∀ t ∈ sphere (0 : ℂ) R, ‖g t‖ ≤ M := by
    intro t ht
    exact hM _ (hmem t (by simp at ht; rw [ht]))
  have hderiv : deriv g 0 = fderiv ℂ f x u := by
    have h1 : HasDerivAt (fun t : ℂ => x + t • u) u 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const u).const_add x
    have hfx : DifferentiableAt ℂ f x :=
      (hd x (mem_ball_self hr)).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))
    have hfx' : HasFDerivAt f (fderiv ℂ f x) (x + (0 : ℂ) • u) := by
      simpa using hfx.hasFDerivAt
    have h2 : HasDerivAt g (fderiv ℂ f x u) 0 := hfx'.comp_hasDerivAt (0 : ℂ) h1
    exact h2.deriv
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdc hbound
  rw [hderiv] at this
  calc ‖fderiv ℂ f x u‖ ≤ M / R := this
    _ = M / r' * ‖u‖ := by rw [hRdef]; field_simp

variable [FiniteDimensional ℂ E]

/-- A function of `(z, θ)` that is jointly continuous on `W × ℝ` (with `W` open) and holomorphic
in `z ∈ W` for each `θ` has a derivative in `z` that is continuous in `θ`. -/
theorem continuous_fderiv_param {W : Set E} (hW : IsOpen W) {G : E → ℝ → F}
    (hc : ContinuousOn (Function.uncurry G) (W ×ˢ univ))
    (hd : ∀ θ, DifferentiableOn ℂ (fun z => G z θ) W) {x₀ : E} (hx₀ : x₀ ∈ W) :
    Continuous fun θ => fderiv ℂ (fun z => G z θ) x₀ := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hW x₀ hx₀
  rw [Metric.continuous_iff]
  intro θ₀ ε hε
  -- uniform continuity of `G` on the compact set `closedBall x₀ (r/2) × [θ₀ - 1, θ₀ + 1]`
  have hK : IsCompact (closedBall x₀ (r / 2) ×ˢ Icc (θ₀ - 1) (θ₀ + 1)) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hKW : closedBall x₀ (r / 2) ×ˢ Icc (θ₀ - 1) (θ₀ + 1) ⊆ W ×ˢ univ := by
    intro p hp
    exact ⟨hrW (closedBall_subset_ball (by linarith) hp.1), trivial⟩
  have huc := hK.uniformContinuousOn_of_continuous (hc.mono hKW)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδK⟩ := huc (ε * (r / 4) / 2) (by positivity)
  refine ⟨min δ 1, lt_min hδ one_pos, fun θ hθ => ?_⟩
  have hθ1 : dist θ θ₀ < 1 := hθ.trans_le (min_le_right _ _)
  have hθδ : dist θ θ₀ < δ := hθ.trans_le (min_le_left _ _)
  have hθmem : θ ∈ Icc (θ₀ - 1) (θ₀ + 1) := by
    rw [Real.dist_eq, abs_lt] at hθ1; constructor <;> linarith
  have hθ₀mem : θ₀ ∈ Icc (θ₀ - 1) (θ₀ + 1) := ⟨by linarith, by linarith⟩
  have hball : ball x₀ (r / 2) ⊆ W := fun y hy => hrW (ball_subset_ball (by linarith) hy)
  have hdx : ∀ θ', DifferentiableAt ℂ (fun z => G z θ') x₀ := fun θ' =>
    (hd θ' x₀ hx₀).differentiableAt (hW.mem_nhds hx₀)
  rw [dist_eq_norm, ← fderiv_sub (hdx θ) (hdx θ₀)]
  have hdiff : DifferentiableOn ℂ (fun z => G z θ - G z θ₀) (ball x₀ (r / 2)) :=
    ((hd θ).mono hball).sub ((hd θ₀).mono hball)
  have hbd : ∀ y ∈ ball x₀ (r / 2), ‖G y θ - G y θ₀‖ ≤ ε * (r / 4) / 2 := by
    intro y hy
    have hy' : y ∈ closedBall x₀ (r / 2) := ball_subset_closedBall hy
    have := hδK (y, θ) ⟨hy', hθmem⟩ (y, θ₀) ⟨hy', hθ₀mem⟩
      (by simpa [Prod.dist_eq] using hθδ)
    rw [dist_eq_norm] at this
    exact this.le
  have := norm_fderiv_le_of_forall_norm_le (r := r / 2) (r' := r / 4) (by positivity)
    (by linarith) hdiff hbd
  calc _ ≤ ε * (r / 4) / 2 / (r / 4) := this
    _ < ε := by field_simp; linarith

/-- **Holomorphic dependence of interval integrals on a parameter.** If `G` is jointly
continuous on `W × ℝ` (with `W` open) and holomorphic in `z ∈ W` for every `θ`, then
`z ↦ ∫ θ in a..b, G z θ` is holomorphic on `W`. -/
theorem differentiableOn_intervalIntegral_of_continuousOn {W : Set E} (hW : IsOpen W)
    {G : E → ℝ → F} (hc : ContinuousOn (Function.uncurry G) (W ×ˢ univ))
    (hd : ∀ θ, DifferentiableOn ℂ (fun z => G z θ) W) (a b : ℝ) :
    DifferentiableOn ℂ (fun z => ∫ θ in a..b, G z θ) W := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  intro x₀ hx₀
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hW x₀ hx₀
  -- a uniform bound on `closedBall x₀ (r/2) × [[a, b]]`
  have hK : IsCompact (closedBall x₀ (r / 2) ×ˢ uIcc a b) :=
    (isCompact_closedBall _ _).prod isCompact_uIcc
  have hKW : closedBall x₀ (r / 2) ×ˢ uIcc a b ⊆ W ×ˢ univ := by
    intro p hp
    exact ⟨hrW (closedBall_subset_ball (by linarith) hp.1), trivial⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hc.mono hKW)
  have hcont : ∀ x ∈ W, Continuous fun θ => G x θ := fun x hx =>
    hc.comp_continuous (continuous_const.prodMk continuous_id) fun θ => ⟨hx, trivial⟩
  have hball4 : ball x₀ (r / 4) ⊆ W := fun y hy => hrW (ball_subset_ball (by linarith) hy)
  have hderiv : HasFDerivAt (fun z => ∫ θ in a..b, G z θ)
      (∫ θ in a..b, fderiv ℂ (fun z => G z θ) x₀) x₀ := by
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F' := fun x θ => fderiv ℂ (fun z => G z θ) x) (bound := fun _ => M / (r / 8))
      (isOpen_ball.mem_nhds (mem_ball_self (by positivity : (0 : ℝ) < r / 4))) ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [hW.mem_nhds hx₀] with x hx
      exact (hcont x hx).aestronglyMeasurable
    · exact (hcont x₀ hx₀).intervalIntegrable _ _
    · exact (continuous_fderiv_param hW hc hd hx₀).aestronglyMeasurable
    · refine Eventually.of_forall fun θ hθ x hx => ?_
      have hsub : ball x (r / 4) ⊆ closedBall x₀ (r / 2) := by
        intro y hy
        rw [mem_ball] at hx hy
        rw [mem_closedBall]
        linarith [dist_triangle y x x₀]
      refine norm_fderiv_le_of_forall_norm_le (r := r / 4) (by positivity) (by linarith)
        ((hd θ).mono (hsub.trans fun y hy => hrW (closedBall_subset_ball (by linarith) hy)))
        fun y hy => ?_
      exact hM (y, θ) ⟨hsub hy, uIoc_subset_uIcc hθ⟩
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun θ _ x hx => ?_
      exact ((hd θ x (hball4 hx)).differentiableAt
        (hW.mem_nhds (hball4 hx))).hasFDerivAt
  exact hderiv.differentiableAt.differentiableWithinAt

/-- **Holomorphic dependence of circle integrals on a parameter.** If `G` is jointly continuous
on `W × sphere c |R|` (with `W` open) and holomorphic in `z ∈ W` for every point of the circle,
then `z ↦ ∮ t in C(c, R), G z t` is holomorphic on `W`. -/
theorem differentiableOn_circleIntegral_of_continuousOn {W : Set E} (hW : IsOpen W)
    {G : E → ℂ → F} {c : ℂ} {R : ℝ}
    (hc : ContinuousOn (Function.uncurry G) (W ×ˢ sphere c |R|))
    (hd : ∀ t ∈ sphere c |R|, DifferentiableOn ℂ (fun z => G z t) W) :
    DifferentiableOn ℂ (fun z => ∮ t in C(c, R), G z t) W := by
  simp only [circleIntegral]
  refine differentiableOn_intervalIntegral_of_continuousOn hW ?_ ?_ 0 (2 * π)
  · have h1 : Continuous fun θ : ℝ => deriv (circleMap c R) θ := by
      simp only [deriv_circleMap]
      exact (continuous_circleMap 0 R).mul continuous_const
    have h2 : ContinuousOn (fun p : E × ℝ => G p.1 (circleMap c R p.2)) (W ×ˢ univ) := by
      refine hc.comp (continuous_fst.prodMk ((continuous_circleMap c R).comp continuous_snd)).continuousOn
        ?_
      intro p hp
      exact ⟨hp.1, circleMap_mem_sphere' c R p.2⟩
    exact (h1.comp continuous_snd).continuousOn.smul h2
  · intro θ
    exact (hd _ (circleMap_mem_sphere' c R θ)).const_smul _

end Langlands.Analysis.SeveralComplex
