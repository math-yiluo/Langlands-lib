import Langlands.Analysis.Meromorphic.ContinuationUniqueness
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Liouville

/-! # Joint continuity after holomorphic division in the spectral variable -/

noncomputable section

open Set Metric Filter Topology

set_option autoImplicit false

namespace Langlands.Analysis.SeveralComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {Y : Type*} [TopologicalSpace Y]

/-- At each point of a connected open set, a nontrivial holomorphic function admits a
complex line disc whose boundary avoids its zeros. The disc may have constant image if
its centre is already a nonzero point. -/
private theorem exists_line_disc_of_differentiableOn {U : Set E} {d : E → ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hd : DifferentiableOn ℂ d U)
    (hne : ∃ s ∈ U, d s ≠ 0) {s₀ : E} (hs₀ : s₀ ∈ U) :
    ∃ v : E, ∃ r : ℝ, 0 < r ∧
      MapsTo (fun z : ℂ => s₀ + z • v) (closedBall 0 r) U ∧
      ∀ z ∈ sphere (0 : ℂ) r, d (s₀ + z • v) ≠ 0 := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU s₀ hs₀
  obtain ⟨w, hw, hwne⟩ := Meromorphic.exists_ne_zero_of_differentiableOn hU hUc hd hne
    isOpen_ball ((ball_subset_ball (by linarith : ε / 2 ≤ ε)).trans hεU)
    ⟨s₀, mem_ball_self (by positivity)⟩
  let v := w - s₀
  let L : ℂ → E := fun z => s₀ + z • v
  have hv : ‖v‖ < ε / 2 := by simpa [v, mem_ball, dist_eq_norm] using hw
  have hLU : MapsTo L (ball 0 2) U := by
    intro z hz
    apply hεU
    rw [mem_ball, show L z = s₀ + z • v from rfl, dist_eq_norm, add_sub_cancel_left, norm_smul]
    have hz' : ‖z‖ < 2 := mem_ball_zero_iff.mp hz
    calc
      _ ≤ 2 * ‖v‖ := mul_le_mul_of_nonneg_right hz'.le (norm_nonneg _)
      _ < ε := by linarith
  have hLd : Differentiable ℂ L :=
    (differentiable_const s₀).add (differentiable_id.smul_const v)
  have hdL : AnalyticOnNhd ℂ (d ∘ L) (ball 0 2) :=
    (hd.comp hLd.differentiableOn hLU).analyticOnNhd isOpen_ball
  have hz₀ : (0 : ℂ) ∈ ball 0 2 := mem_ball_self two_pos
  have hz₁ : (1 : ℂ) ∈ ball 0 2 := by simp [mem_ball, dist_zero_right]
  have hgood : ∀ᶠ z in 𝓝[≠] (0 : ℂ), d (L z) ≠ 0 := by
    by_contra h
    have hz : (d ∘ L) 1 = 0 := hdL.eqOn_zero_of_preconnected_of_frequently_eq_zero
      (convex_ball (0 : ℂ) 2).isPreconnected hz₀ (by simpa using not_eventually.mp h) hz₁
    exact hwne (by simpa [L, v] using hz)
  obtain ⟨δ, hδ, hδd⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hgood)
  let r := min δ 2 / 2
  have hr : 0 < r := half_pos (lt_min hδ two_pos)
  have hrδ : r < δ := (half_lt_self (lt_min hδ two_pos)).trans_le (min_le_left _ _)
  have hr2 : r < 2 := (half_lt_self (lt_min hδ two_pos)).trans_le (min_le_right _ _)
  refine ⟨v, r, hr, fun z hz => hLU (closedBall_subset_ball hr2 hz), ?_⟩
  intro z hz
  have hzr : dist z 0 = r := mem_sphere.mp hz
  apply hδd (by simpa only [hzr] using hrδ : dist z 0 < δ)
  intro h
  have hz0 : z = 0 := h
  exact hr.ne' (by simpa [hz0] using hzr.symm)

/-- If `h` is holomorphic in its first variable and a nontrivial holomorphic factor times
`h` is jointly continuous, then `h` is jointly continuous. The second variable ranges over
an arbitrary topological space. -/
theorem continuousOn_of_differentiableOn_of_mul {U : Set E} {d : E → ℂ} {h : E → Y → ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hd : DifferentiableOn ℂ d U)
    (hdne : ∃ s ∈ U, d s ≠ 0) (hh : ∀ y, DifferentiableOn ℂ (fun s => h s y) U)
    (hc : ContinuousOn (fun q : E × Y => d q.1 * h q.1 q.2) (U ×ˢ univ)) :
    ContinuousOn (fun q : E × Y => h q.1 q.2) (U ×ˢ univ) := by
  have hdiv (q : E × Y) (hq : q.1 ∈ U) (hne : d q.1 ≠ 0) :
      ContinuousAt (fun q : E × Y => h q.1 q.2) q := by
    have hno : ContinuousAt (fun q : E × Y => d q.1 * h q.1 q.2) q :=
      hc.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hq, mem_univ _⟩)
    have hden := (hd.continuousOn.continuousAt (hU.mem_nhds hq)).comp continuousAt_fst
    refine (hno.div hden hne).congr ?_
    filter_upwards [hden.eventually_ne hne] with x hx
    change d x.1 ≠ 0 at hx
    change d x.1 * h x.1 x.2 / d x.1 = h x.1 x.2
    rw [mul_comm, mul_div_cancel_right₀ _ hx]
  rintro ⟨s₀, y₀⟩ ⟨hs₀, -⟩
  obtain ⟨v, r, hr, hdisc, hcircle⟩ := exists_line_disc_of_differentiableOn hU hUc hd hdne hs₀
  let T : (E × Y) × ℂ → E × Y := fun p => (p.1.1 + p.2 • v, p.1.2)
  let T₀ : (E × Y) × ℂ → E × Y := fun p => (s₀ + p.2 • v, y₀)
  have hT : Continuous T := by dsimp [T]; fun_prop
  have hT₀ : Continuous T₀ := by dsimp [T₀]; fun_prop
  have hn : ∀ᶠ p : E × Y in 𝓝 (s₀, y₀),
      MapsTo (fun z : ℂ => p.1 + z • v) (closedBall 0 r) U := by
    refine (isCompact_closedBall (0 : ℂ) r).eventually_forall_of_forall_eventually ?_
    intro z hz
    exact (continuous_fst.comp hT).continuousAt.eventually_mem (hU.mem_nhds (hdisc hz))
  apply ContinuousAt.continuousWithinAt
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hb : ∀ᶠ p : E × Y in 𝓝 (s₀, y₀), ∀ z ∈ sphere (0 : ℂ) r,
      ‖h (p.1 + z • v) p.2 - h (s₀ + z • v) y₀‖ < ε / 2 := by
    refine (isCompact_sphere (0 : ℂ) r).eventually_forall_of_forall_eventually ?_
    intro z hz
    have ha := hdiv (s₀ + z • v, y₀) (hdisc (sphere_subset_closedBall hz)) (hcircle z hz)
    have h1 : ContinuousAt (fun p : (E × Y) × ℂ => h (p.1.1 + p.2 • v) p.1.2) ((s₀, y₀), z) :=
      ContinuousAt.comp_of_eq (f := T) ha hT.continuousAt rfl
    have h2 : ContinuousAt (fun p : (E × Y) × ℂ => h (s₀ + p.2 • v) y₀) ((s₀, y₀), z) :=
      ContinuousAt.comp_of_eq (f := T₀) ha hT₀.continuousAt rfl
    exact (h1.sub h2).norm.eventually_lt (continuousAt_const (y := ε / 2)) (by simp [hε])
  filter_upwards [hn, hb] with p hp hpb
  let F : ℂ → ℂ := fun z => h (p.1 + z • v) p.2 - h (s₀ + z • v) y₀
  have hFd : DifferentiableOn ℂ F (closedBall 0 r) :=
    ((hh p.2).comp ((differentiable_const _).add (differentiable_id.smul_const v)).differentiableOn hp).sub
      ((hh y₀).comp ((differentiable_const _).add (differentiable_id.smul_const v)).differentiableOn hdisc)
  have hF := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (f := F) 0 hr
    (hFd.diffContOnCl_ball Subset.rfl) (fun z hz => (hpb z hz).le)
  have hF' : ‖F 0‖ ≤ ε / 2 := by simpa using hF
  rw [dist_eq_norm]
  exact (by simpa [F] using hF' : ‖h p.1 p.2 - h s₀ y₀‖ ≤ ε / 2).trans_lt (half_lt_self hε)

end Langlands.Analysis.SeveralComplex
