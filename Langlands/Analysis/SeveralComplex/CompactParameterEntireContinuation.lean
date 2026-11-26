import Langlands.Analysis.SeveralComplex.Hartogs.Basic
import Langlands.Analysis.SeveralComplex.HolomorphicCoefficientDecay
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! # Entire slice continuation from an open disk of parameters -/

noncomputable section

open Metric Set Filter
open scoped Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analysis.SeveralComplex

private theorem halfPlane_ball_subset (σ : ℝ) :
    ball ((σ + 2 : ℝ) : ℂ) 2 ⊆ {s : ℂ | σ < s.re} := by
  intro w hw
  have hn := mem_ball_iff_norm.mp hw
  have habs := (Complex.abs_re_le_norm _).trans_lt hn
  rw [Complex.sub_re, Complex.ofReal_re] at habs
  change σ < w.re
  linarith [(abs_lt.mp habs).1]

private theorem exists_series_norm_bound {c : ℕ → ℂ → ℂ} {A : ℝ}
    (hA : ∀ n z, z ∈ closedBall 0 2 → ‖c n z‖ ≤ A)
    (hc : ∀ b : ℝ, 0 < b → ∀ᶠ n in atTop, ∀ z ∈ closedBall 0 (3 / 2), ‖c n z‖ ≤ b ^ n)
    (s₀ : ℂ) {R : ℝ} (hR : 0 < R) :
    ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n z s, z ∈ closedBall 0 (3 / 2) → ‖s - s₀‖ ≤ R → ‖c n z * (s - s₀) ^ n‖ ≤ u n := by
  let B := (1 / 2 : ℝ) / R
  have hB : 0 < B := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hc B hB)
  let u (n : ℕ) : ℝ := if N ≤ n then (1 / 2 : ℝ) ^ n else A * R ^ n
  have hu : Summable u := by
    apply (summable_geometric_of_lt_one (show 0 ≤ (1 / 2 : ℝ) by norm_num) (by norm_num)).congr_cofinite
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [u, ite_eq_left hn]
  refine ⟨u, hu, fun n z s hz hs => ?_⟩
  rw [norm_mul, norm_pow]
  have hs' : ‖s - s₀‖ ^ n ≤ R ^ n := pow_le_pow_left₀ (norm_nonneg _) hs n
  have hA₀ : 0 ≤ A := (norm_nonneg _).trans (hA 0 0 (mem_closedBall_self (by norm_num)))
  by_cases hn : N ≤ n
  · simp only [u, ite_eq_left hn]
    calc
      _ ≤ B ^ n * R ^ n := mul_le_mul (hN n hn z hz) hs' (by positivity) (by positivity)
      _ = (1 / 2 : ℝ) ^ n := by
        rw [← mul_pow]
        dsimp only [B]
        rw [div_mul_cancel₀ _ hR.ne']
  · simp only [u, ite_eq_right hn]
    exact mul_le_mul (hA n z (closedBall_subset_closedBall (by norm_num : (3 / 2 : ℝ) ≤ 2) hz))
      hs' (by positivity) hA₀

/-- A right half-plane family with entire spectral slices near parameter `0` has a
joint holomorphic continuation on the parameter disk of radius `3 / 2` times `ℂ`. -/
def CompactParameterJointEntireContinuationStatement : Prop :=
  ∀ (F : ℂ × ℂ → ℂ) (σ : ℝ),
    DifferentiableOn ℂ F (ball 0 3 ×ˢ {s : ℂ | σ < s.re}) →
    (∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball 0 δ, ∃ N : ℂ → ℂ, Differentiable ℂ N ∧
      EqOn N (fun s => F (z, s)) {s : ℂ | σ < s.re}) →
    ∃ N : ℂ × ℂ → ℂ, DifferentiableOn ℂ N (ball 0 (3 / 2) ×ˢ univ) ∧
      EqOn N F (ball 0 (3 / 2) ×ˢ {s : ℂ | σ < s.re})

set_option maxHeartbeats 700000 in
theorem compactParameterJointEntireContinuation :
    CompactParameterJointEntireContinuationStatement := by
  intro F σ hF ⟨δ, hδ, hInit⟩
  let rightHalf : Set ℂ := {s : ℂ | σ < s.re}
  let P : Set ℂ := ball 0 3
  let Q : Set ℂ := ball 0 (3 / 2)
  let s₀ : ℂ := ((σ + 2 : ℝ) : ℂ)
  let c (n : ℕ) (z : ℂ) := taylorCoeff F s₀ 1 n z
  have hPlus : IsOpen rightHalf := isOpen_lt continuous_const Complex.continuous_re
  have hsBall : ball s₀ 2 ⊆ rightHalf := halfPlane_ball_subset σ
  have hs₀ : s₀ ∈ rightHalf := hsBall (mem_ball_self (by norm_num))
  have hFs (z : ℂ) (hz : z ∈ P) :
      DifferentiableOn ℂ (fun s => F (z, s)) rightHalf :=
    hF.comp ((differentiable_const z).prodMk differentiable_id).differentiableOn (fun _ hs => ⟨hz, hs⟩)
  have hFz (s : ℂ) (hs : s ∈ rightHalf) :
      DifferentiableOn ℂ (fun z => F (z, s)) P :=
    hF.comp (differentiable_id.prodMk (differentiable_const s)).differentiableOn (fun _ hz => ⟨hz, hs⟩)
  have hC (n : ℕ) : DifferentiableOn ℂ (c n) P :=
    differentiableOn_taylorCoeff (B := P) isOpen_ball (f := F) (w₁ := s₀)
      one_pos (by norm_num : (1 : ℝ) < 2) (by norm_num : (1 : ℝ) < 2)
      (fun s hs => hFz s (hsBall hs)) (hF.continuousOn.mono (prod_mono subset_rfl hsBall)) n
  have hSphere : sphere s₀ 1 ⊆ rightHalf := (sphere_subset_ball (by norm_num : (1 : ℝ) < 2)).trans hsBall
  obtain ⟨A, hA⟩ := ((isCompact_closedBall (0 : ℂ) 2).prod (isCompact_sphere s₀ 1)).exists_bound_of_continuousOn
    (hF.continuousOn.mono
      (prod_mono (closedBall_subset_ball (by norm_num)) hSphere))
  have hBound (n : ℕ) (z : ℂ) (hz : z ∈ closedBall 0 2) : ‖c n z‖ ≤ A := by
    simpa only [c, one_pow, div_one] using
      norm_taylorCoeff_le (f := F) (w₁ := s₀) one_pos (z := z)
        (fun w hw => hA (z, w) ⟨hz, hw⟩) n
  have hDecay : ∀ b : ℝ, 0 < b → ∀ᶠ n in atTop, ∀ z ∈ closedBall 0 (3 / 2), ‖c n z‖ ≤ b ^ n := by
    refine holomorphicCoefficientDecay c hC ⟨A, hBound⟩ ?_
    let e := min δ 1
    refine ⟨e, lt_min hδ one_pos, fun z hz b hb => ?_⟩
    have hz₃ : z ∈ P := ball_subset_ball ((min_le_right _ _).trans (by norm_num)) hz
    obtain ⟨N, hN, hNplus⟩ := hInit z (ball_subset_ball (min_le_left _ _) hz)
    let T : ℝ := 2 / b
    have hT : 0 < T := by positivity
    obtain ⟨M, hM⟩ := (isCompact_sphere s₀ T).exists_bound_of_continuousOn hN.continuous.continuousOn
    have heq : (fun s => F (z, s)) =ᶠ[𝓝 s₀] N :=
      Filter.Eventually.mono (hPlus.mem_nhds hs₀) fun _ hs => (hNplus hs).symm
    have hCoeff (n : ℕ) :
        c n z = taylorCoeff (fun p : ℂ × ℂ => N p.2) s₀ T n z := by
      dsimp only [c]
      rw [taylorCoeff_eq one_pos (by norm_num : (1 : ℝ) < 2) ((hFs z hz₃).mono hsBall),
        taylorCoeff_eq hT (lt_add_one T) hN.differentiableOn, heq.iteratedDeriv_eq n]
    have hMpow : ∀ᶠ n : ℕ in atTop, M ≤ (2 : ℝ) ^ n :=
      (tendsto_atTop.1 (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))) M
    filter_upwards [hMpow] with n hn
    rw [hCoeff]
    refine (norm_taylorCoeff_le hT hM n).trans ((div_le_iff₀ (by positivity)).2 ?_)
    rw [← mul_pow, show b * T = 2 by dsimp only [T]; field_simp]
    exact hn
  let N (z s : ℂ) := ∑' n : ℕ, c n z * (s - s₀) ^ n
  have hNs (z : ℂ) (hz : z ∈ Q) : Differentiable ℂ (N z) := by
    intro s
    let R := ‖s - s₀‖ + 1
    have hR : 0 < R := by positivity
    obtain ⟨u, hu, hU⟩ := exists_series_norm_bound hBound hDecay s₀ hR
    have hD : DifferentiableOn ℂ (N z) (ball s₀ R) :=
      Complex.differentiableOn_tsum_of_summable_norm hu
        (fun n => ((differentiable_const (c n z)).mul ((differentiable_id.sub_const s₀).pow n)).differentiableOn)
        isOpen_ball (fun n w hw => hU n z w (ball_subset_closedBall hz) (mem_ball_iff_norm.mp hw).le)
    exact hD.differentiableAt (isOpen_ball.mem_nhds (mem_ball_iff_norm.mpr (lt_add_one _)))
  have hNz (s : ℂ) : DifferentiableOn ℂ (fun z => N z s) Q := by
    let R := ‖s - s₀‖ + 1
    have hR : 0 < R := by positivity
    obtain ⟨u, hu, hU⟩ := exists_series_norm_bound hBound hDecay s₀ hR
    refine Complex.differentiableOn_tsum_of_summable_norm hu
      (fun n => ((hC n).mono (ball_subset_ball (by norm_num))).mul_const _) isOpen_ball ?_
    exact fun n z hz => hU n z s (ball_subset_closedBall hz) (le_of_lt (lt_add_one _))
  have hNF (z : ℂ) (hz : z ∈ Q) : EqOn (N z) (fun s => F (z, s)) rightHalf := by
    have hzP : z ∈ P := ball_subset_ball (by norm_num : (3 / 2 : ℝ) ≤ 3) hz
    apply ((hNs z hz).differentiableOn.analyticOnNhd hPlus).eqOn_of_preconnected_of_eventuallyEq
      ((hFs z hzP).analyticOnNhd hPlus) ((convex_halfSpace_re_gt σ).isPreconnected) hs₀
    filter_upwards [ball_mem_nhds s₀ (show (0 : ℝ) < 2 by norm_num)] with s hs
    exact (hasSum_taylorCoeff one_pos (by norm_num : (1 : ℝ) < 2) ((hFs z hzP).mono hsBall) hs).tsum_eq
  exact ⟨fun p => N p.1 p.2,
    differentiableOn_prod_of_separately isOpen_ball isOpen_univ
      (fun s _ => hNz s) (fun z hz => (hNs z hz).differentiableOn),
    fun p hp => hNF p.1 hp.1 hp.2⟩

/-- Holomorphic right and left half-plane functions of two variables at parameter `1`
have a common entire continuation if their slices near parameter `0` do.
Both half-planes are uniform on the parameter disk of radius `3`. -/
def CompactParameterEntireContinuationStatement : Prop :=
  ∀ (F G : ℂ × ℂ → ℂ) (σ τ : ℝ),
    DifferentiableOn ℂ F (ball 0 3 ×ˢ {s : ℂ | σ < s.re}) →
    DifferentiableOn ℂ G (ball 0 3 ×ˢ {s : ℂ | s.re < τ}) →
    (∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball 0 δ, ∃ N : ℂ → ℂ, Differentiable ℂ N ∧
      EqOn N (fun s => F (z, s)) {s : ℂ | σ < s.re} ∧
      EqOn N (fun s => G (z, s)) {s : ℂ | s.re < τ}) →
    ∃ N : ℂ → ℂ, Differentiable ℂ N ∧
      EqOn N (fun s => F (1, s)) {s : ℂ | σ < s.re} ∧
      EqOn N (fun s => G (1, s)) {s : ℂ | s.re < τ}

theorem compactParameterEntireContinuation : CompactParameterEntireContinuationStatement := by
  intro F G σ τ hF hG ⟨δ, hδ, hInit⟩
  obtain ⟨N, hN, hNF⟩ := compactParameterJointEntireContinuation F σ hF
    ⟨δ, hδ, fun z hz => by
      obtain ⟨N, hN, hNF, _⟩ := hInit z hz
      exact ⟨N, hN, hNF⟩⟩
  let Q : Set ℂ := ball 0 (3 / 2)
  have hNs (z : ℂ) (hz : z ∈ Q) : Differentiable ℂ (fun s => N (z, s)) :=
    differentiableOn_univ.mp
      (hN.comp ((differentiable_const z).prodMk differentiable_id).differentiableOn
        (fun _ hs => ⟨hz, hs⟩))
  have hNz (s : ℂ) : DifferentiableOn ℂ (fun z => N (z, s)) Q :=
    hN.comp (differentiable_id.prodMk (differentiable_const s)).differentiableOn
      (fun _ hz => ⟨hz, mem_univ _⟩)
  have hNG (s : ℂ) (hs : s.re < τ) : EqOn (fun z => N (z, s)) (fun z => G (z, s)) Q := by
    have hGz : DifferentiableOn ℂ (fun z => G (z, s)) Q :=
      hG.comp (differentiable_id.prodMk (differentiable_const s)).differentiableOn
        (fun _ hz => ⟨ball_subset_ball (by norm_num : (3 / 2 : ℝ) ≤ 3) hz, hs⟩)
    apply ((hNz s).analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq
      (hGz.analyticOnNhd isOpen_ball) ((convex_ball (0 : ℂ) (3 / 2)).isPreconnected)
      (mem_ball_self (by norm_num : (0 : ℝ) < 3 / 2))
    filter_upwards [ball_mem_nhds (0 : ℂ) hδ,
      ball_mem_nhds (0 : ℂ) (show (0 : ℝ) < 3 / 2 by norm_num)] with z hzδ hz
    obtain ⟨P₀, hP₀, hP₀plus, hP₀minus⟩ := hInit z hzδ
    have heq : (fun s => N (z, s)) = P₀ := by
      let s₀ : ℂ := ((σ + 2 : ℝ) : ℂ)
      apply AnalyticOnNhd.eq_of_eventuallyEq
        (fun w _ => (hNs z hz).analyticAt w)
        (fun w _ => hP₀.analyticAt w) (z₀ := s₀)
      filter_upwards [ball_mem_nhds s₀ (show (0 : ℝ) < 2 by norm_num)] with w hw
      have hw' := halfPlane_ball_subset σ hw
      exact (hNF (show (z, w) ∈ Q ×ˢ {s : ℂ | σ < s.re} from ⟨hz, hw'⟩)).trans
        (hP₀plus hw').symm
    exact (congrFun heq s).trans (hP₀minus hs)
  have h1 : (1 : ℂ) ∈ Q := by
    exact mem_ball_zero_iff.2 (by norm_num)
  exact ⟨fun s => N (1, s), hNs 1 h1, fun _ hs => hNF ⟨h1, hs⟩, fun s hs => hNG s hs h1⟩

end Langlands.Analysis.SeveralComplex
