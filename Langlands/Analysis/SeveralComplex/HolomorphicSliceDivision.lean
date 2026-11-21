import Langlands.Analysis.Meromorphic.ImaginaryHyperplaneDivision
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.MeanValue

/-! # Holomorphic division from analytic division on parallel complex lines -/

noncomputable section

open Set Filter Metric
open scoped Topology

set_option autoImplicit false

namespace Langlands.Analysis

private theorem exists_analyticOnNhd_quotient_on_line
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U) {den num : ℂ → ℂ}
    (hd : AnalyticOnNhd ℂ den U) (hdne : ∃ z ∈ U, den z ≠ 0)
    (hdiv : ∀ z ∈ U, ∃ b : ℂ → ℂ, AnalyticAt ℂ b z ∧ num =ᶠ[𝓝 z] den * b) :
    ∃ q : ℂ → ℂ, AnalyticOnNhd ℂ q U ∧ EqOn (den * q) num U := by
  classical
  obtain ⟨z, hz, hzne⟩ := hdne
  have hfinite (t : ℂ) (ht : t ∈ U) : analyticOrderAt den t ≠ ⊤ :=
    hd.analyticOrderAt_ne_top_of_isPreconnected hUc hz ht
      ((hd z hz).analyticOrderAt_eq_zero.mpr hzne ▸ ENat.zero_ne_top)
  let q (t : ℂ) : ℂ := if ht : t ∈ U then (hdiv t ht).choose t else 0
  have hq : EqOn (den * q) num U := by
    intro t ht
    exact (by simpa only [q, dite_eq_left ht, Pi.mul_apply] using
      ((hdiv t ht).choose_spec.2.self_of_nhds).symm)
  refine ⟨q, fun t ht => ?_, hq⟩
  have hn : ∀ᶠ x in 𝓝[≠] t, den x ≠ 0 :=
    ((hd t ht).eventually_eq_zero_or_eventually_ne_zero).resolve_left
      (fun h => hfinite t ht (analyticOrderAt_eq_top.mpr h))
  rw [eventually_nhdsWithin_iff] at hn
  obtain ⟨ha, heq⟩ := (hdiv t ht).choose_spec
  refine (analyticAt_congr ?_).mpr ha
  filter_upwards [hU.mem_nhds ht, heq, hn] with x hx hxeq hxne
  by_cases hxt : x = t
  · subst x
    simp [q, ht]
  · exact mul_left_cancel₀ (hxne hxt) ((hq hx).trans hxeq)

section SeveralVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Translate one circle of complex slices and average the quotient along it. -/
def circleDivision (den num : E → ℂ) (u : E) (r : ℝ) (s : E) : ℂ :=
  Real.circleAverage (fun z : ℂ => num (s + z • u) / den (s + z • u)) 0 r

/-- Around a point where the scalar holomorphic denominator has a nonzero germ,
one can choose a disk of parallel complex lines with nonvanishing denominator
on the chosen circle for every nearby base point. -/
theorem exists_open_division_circle {U : Set E} (hU : IsOpen U) {s₀ : E} (hs₀ : s₀ ∈ U)
    {den : E → ℂ} (hd : DifferentiableOn ℂ den U) (hdne : ¬ den =ᶠ[𝓝 s₀] 0) :
    ∃ (u : E) (r : ℝ) (V : Set E), IsOpen V ∧ s₀ ∈ V ∧ V ⊆ U ∧ 0 < r ∧ r < 2 ∧
      (∀ s ∈ V, MapsTo (fun z : ℂ => s + z • u) (ball 0 2) U) ∧
      ∀ s ∈ V, ∀ z ∈ sphere (0 : ℂ) r, den (s + z • u) ≠ 0 := by
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU s₀ hs₀
  have hδ' : 0 < δ / 4 := by positivity
  obtain ⟨y, hy, hyne⟩ : ∃ y ∈ ball s₀ (δ / 4), den y ≠ 0 := by
    by_contra! heq
    exact hdne (eventually_of_mem (ball_mem_nhds s₀ hδ') heq)
  let u := y - s₀
  have hu : ‖u‖ < δ / 4 := by simpa only [u, mem_ball, dist_eq_norm] using hy
  have hline (s : E) (hs : s ∈ ball s₀ (δ / 4)) :
      MapsTo (fun z : ℂ => s + z • u) (ball 0 2) U := by
    intro z hz
    apply hδU
    have hzs : dist (s + z • u) s = ‖z‖ * ‖u‖ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
    have hz' : ‖z‖ ≤ 2 := le_of_lt (by simpa only [mem_ball, dist_zero_right] using hz)
    have hsz := mul_le_mul_of_nonneg_right hz' (norm_nonneg u)
    have ht := dist_triangle (s + z • u) s s₀
    rw [hzs] at ht
    exact mem_ball.mpr (by linarith [mem_ball.mp hs])
  let a (z : ℂ) := den (s₀ + z • u)
  have ha : AnalyticOnNhd ℂ a (ball 0 2) :=
    ((hd.comp (by fun_prop) (hline s₀ (mem_ball_self hδ')))).analyticOnNhd isOpen_ball
  have h1 : (1 : ℂ) ∈ ball 0 2 := by simp [mem_ball, dist_zero_right]
  have h0 : (0 : ℂ) ∈ ball 0 2 := mem_ball_self (by norm_num)
  have hane : a 1 ≠ 0 := by
    simpa only [a, u, one_smul, add_sub_cancel] using hyne
  have hfinite : analyticOrderAt a 0 ≠ ⊤ :=
    ha.analyticOrderAt_ne_top_of_isPreconnected (convex_ball (0 : ℂ) 2).isPreconnected
      h1 h0 ((ha 1 h1).analyticOrderAt_eq_zero.mpr hane ▸ ENat.zero_ne_top)
  have hev := (ha 0 h0).eventually_eq_zero_or_eventually_ne_zero.resolve_left
    (fun h => hfinite (analyticOrderAt_eq_top.mpr h))
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨ε, hε, hεa⟩ := Metric.mem_nhds_iff.mp hev
  let r := min ε 1 / 2
  have hr : 0 < r := half_pos (lt_min hε zero_lt_one)
  have hrε : r < ε := (half_lt_self (lt_min hε zero_lt_one)).trans_le (min_le_left _ _)
  have hr2 : r < 2 := by
    have := min_le_right ε (1 : ℝ)
    dsimp [r]
    linarith
  let K := (fun z : ℂ => s₀ + z • u) '' sphere (0 : ℂ) r
  have hK : IsCompact K := (isCompact_sphere _ _).image (by fun_prop)
  let D := U ∩ den ⁻¹' ({0}ᶜ : Set ℂ)
  have hD : IsOpen D := hd.continuousOn.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
  have hKD : K ⊆ D := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' : ‖z‖ = r := by simpa only [mem_sphere, dist_zero_right] using hz
    have hz0 : z ≠ 0 := fun h => hr.ne' (by simpa [h] using hz'.symm)
    refine ⟨hline s₀ (mem_ball_self hδ') (by simpa only [mem_ball, dist_zero_right, hz'] using hr2), ?_⟩
    exact hεa (show z ∈ ball 0 ε by simpa only [mem_ball, dist_zero_right, hz'] using hrε) hz0
  obtain ⟨τ, hτ, hτD⟩ := hK.exists_cthickening_subset_open hD hKD
  let V := ball s₀ (min τ (δ / 4))
  have hVs : V ⊆ ball s₀ (δ / 4) := ball_subset_ball (min_le_right _ _)
  refine ⟨u, r, V, isOpen_ball, mem_ball_self (lt_min hτ hδ'), ?_, hr, hr2,
    fun s hs => hline s (hVs hs), ?_⟩
  · intro s hs
    simpa only [zero_smul, add_zero] using hline s (hVs hs) h0
  · intro s hs z hz
    apply And.right (hτD (mem_cthickening_of_dist_le (s + z • u) (s₀ + z • u) τ K
      ⟨z, hz, rfl⟩ ?_))
    rw [dist_add_right]
    exact (mem_ball.mp hs).le.trans (min_le_left _ _)

/-- The circle division is holomorphic where the translated circle lies in the
holomorphy domain and avoids zeros of the denominator. -/
theorem differentiableOn_circleDivision [FiniteDimensional ℂ E] {U V : Set E} (hU : IsOpen U)
    {den num : E → ℂ} (hd : DifferentiableOn ℂ den U) (hn : DifferentiableOn ℂ num U)
    (u : E) {r : ℝ} (hr : 0 < r)
    (hV : ∀ s ∈ V, ∀ z ∈ sphere (0 : ℂ) r, s + z • u ∈ U ∧ den (s + z • u) ≠ 0) :
    DifferentiableOn ℂ (circleDivision den num u r) V := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let D := U ∩ den ⁻¹' ({0}ᶜ : Set ℂ)
  have hD : IsOpen D := hd.continuousOn.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
  have hDU : D ⊆ U := inter_subset_left
  have hquot : DifferentiableOn ℂ (fun t => num t / den t) D := by
    simp only [div_eq_mul_inv]
    exact (hn.mono hDU).mul ((hd.mono hDU).inv (fun _ ht => ht.2))
  intro s hs
  exact (Meromorphic.ImaginaryHyperplane.differentiableAt_circleAverage_comp_add
    hD hquot u r
    (fun z hz => hV s hs z (by simpa [abs_of_pos hr] using hz))).differentiableWithinAt

/-- Recover the quotient at a disk center by circle averaging provided division
exists as an analytic germ at every point of the disk. At the center the equality
holds after multiplication by the denominator. -/
theorem mul_circleDivision_eq {U : Set E} {den num : E → ℂ}
    (hd : DifferentiableOn ℂ den U) (u s : E) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hline : MapsTo (fun z : ℂ => s + z • u) (ball 0 R) U)
    (hnz : ∀ z ∈ sphere (0 : ℂ) r, den (s + z • u) ≠ 0)
    (hdiv : ∀ z ∈ ball (0 : ℂ) R, ∃ b : ℂ → ℂ, AnalyticAt ℂ b z ∧
      (fun t : ℂ => num (s + t • u)) =ᶠ[𝓝 z] fun t => den (s + t • u) * b t) :
    den s * circleDivision den num u r s = num s := by
  let d (z : ℂ) := den (s + z • u)
  let n (z : ℂ) := num (s + z • u)
  have ha : AnalyticOnNhd ℂ d (ball 0 R) :=
    (hd.comp (by fun_prop) hline).analyticOnNhd isOpen_ball
  have hnon : ∃ z ∈ ball (0 : ℂ) R, d z ≠ 0 := by
    have hsp : (r : ℂ) ∈ sphere 0 r := by simp [hr.le]
    exact ⟨r, mem_ball.mpr ((mem_sphere.mp hsp).trans_lt hrR), hnz _ hsp⟩
  obtain ⟨q, hq, hqeq⟩ := exists_analyticOnNhd_quotient_on_line isOpen_ball
    (convex_ball (0 : ℂ) R).isPreconnected ha hnon hdiv
  have hmean : Real.circleAverage q 0 r = q 0 := by
    have hsub : closure (ball (0 : ℂ) |r|) ⊆ ball 0 R :=
      (closure_ball_subset_closedBall.trans (closedBall_subset_ball (by simpa [abs_of_pos hr] using hrR)))
    exact ((hq.mono hsub).differentiableOn.diffContOnCl).circleAverage
  have havg : circleDivision den num u r s = q 0 := by
    unfold circleDivision
    rw [← hmean]
    apply Real.circleAverage_congr_sphere
    intro z hz
    have hz' : z ∈ sphere (0 : ℂ) r := by simpa [abs_of_pos hr] using hz
    exact (div_eq_iff (hnz z hz')).mpr (by
      have hqz := hqeq (mem_ball.mpr ((mem_sphere.mp hz').trans_lt hrR))
      exact hqz.symm.trans (mul_comm _ _))
  rw [havg]
  have h0 : (0 : ℂ) ∈ ball 0 R := mem_ball_self (hr.trans hrR)
  simpa only [d, n, Pi.mul_apply, zero_smul, add_zero] using hqeq h0

end SeveralVariables

end Langlands.Analysis
