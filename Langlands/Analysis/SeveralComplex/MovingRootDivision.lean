import Langlands.Analysis.SeveralComplex.HolomorphicSliceDivision

/-! # Holomorphic division by a polynomial with varying roots -/

noncomputable section

open Filter Metric Set
open scoped Topology

set_option autoImplicit false

namespace Langlands.Analysis.SeveralComplex

/-- The monic polynomial in the second variable whose roots depend on the first.
Repeated entries in the list give repeated factors. -/
def movingRootProduct (roots : List (ℂ → ℂ)) (w : ℂ × ℂ) : ℂ :=
  (roots.map fun r => w.2 - r w.1).prod

private theorem differentiableOn_movingRootProduct {U : Set ℂ} {roots : List (ℂ → ℂ)}
    (hroots : ∀ r ∈ roots, DifferentiableOn ℂ r U) :
    DifferentiableOn ℂ (movingRootProduct roots) (U ×ˢ (univ : Set ℂ)) := by
  induction roots with
  | nil => exact differentiableOn_const _
  | cons r rs ih =>
      have hr := hroots r (List.mem_cons_self ..)
      have ht := ih (fun t ht => hroots t (List.mem_cons_of_mem _ ht))
      change DifferentiableOn ℂ (fun w : ℂ × ℂ => (w.2 - r w.1) * movingRootProduct rs w) _
      exact (differentiable_snd.differentiableOn.sub
        (hr.comp differentiable_fst.differentiableOn fun _ hw => hw.1)).mul ht

private theorem exists_bound_roots {U K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U)
    {roots : List (ℂ → ℂ)} (hroots : ∀ r ∈ roots, DifferentiableOn ℂ r U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ roots, ∀ z ∈ K, ‖r z‖ ≤ B := by
  induction roots with
  | nil => exact ⟨0, le_rfl, by simp⟩
  | cons r rs ih =>
      obtain ⟨B, hB, hb⟩ := ih (fun t ht => hroots t (List.mem_cons_of_mem _ ht))
      obtain ⟨C, hc⟩ := hK.exists_bound_of_continuousOn
        ((hroots r (List.mem_cons_self ..)).continuousOn.mono hKU)
      refine ⟨max B C, hB.trans (le_max_left _ _), fun t ht z hz => ?_⟩
      rcases List.mem_cons.mp ht with rfl | ht
      · exact (hc z hz).trans (le_max_right _ _)
      · exact (hb t ht z hz).trans (le_max_left _ _)

private theorem movingRootProduct_ne_zero (roots : List (ℂ → ℂ)) (z s : ℂ)
    (h : ∀ r ∈ roots, s ≠ r z) : movingRootProduct roots (z, s) ≠ 0 := by
  induction roots with
  | nil => exact one_ne_zero
  | cons r rs ih =>
      exact mul_ne_zero (sub_ne_zero.mpr (h r (List.mem_cons_self ..)))
        (ih (fun t ht => h t (List.mem_cons_of_mem _ ht)))

private theorem movingRootProduct_eventually_ne_zero
    (roots : List (ℂ → ℂ)) (z s : ℂ) :
    ∀ᶠ t in 𝓝[≠] s, movingRootProduct roots (z, t) ≠ 0 := by
  induction roots with
  | nil => exact Eventually.of_forall fun _ => one_ne_zero
  | cons r rs ih =>
      have hr : ∀ᶠ t in 𝓝[≠] s, t ≠ r z := by
        by_cases h : s = r z
        · rw [← h]
          exact self_mem_nhdsWithin
        · have : ∀ᶠ t in 𝓝 s, t ≠ r z := isClosed_singleton.isOpen_compl.mem_nhds h
          exact this.filter_mono nhdsWithin_le_nhds
      filter_upwards [hr, ih] with t ht hts
      exact mul_ne_zero (sub_ne_zero.mpr ht) hts

private theorem exists_local_quotient {R : ℝ} (hR : 0 < R) {F : ℂ × ℂ → ℂ}
    {roots : List (ℂ → ℂ)}
    (hF : DifferentiableOn ℂ F (ball 0 R ×ˢ (univ : Set ℂ)))
    (hroots : ∀ r ∈ roots, DifferentiableOn ℂ r (ball 0 R))
    (hquot : ∃ᶠ z in 𝓝[≠] (0 : ℂ), ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      ∀ s, F (z, s) = movingRootProduct roots (z, s) * G s)
    {z s : ℂ} (hz : z ∈ ball 0 R) :
    ∃ R' : ℝ, z ∈ ball 0 R' ∧
      ∃ Q : ℂ × ℂ → ℂ, DifferentiableOn ℂ Q (ball 0 R' ×ˢ ball s 1) ∧
        ∀ w ∈ ball 0 R' ×ˢ ball s 1, F w = movingRootProduct roots w * Q w := by
  have hzn : ‖z‖ < R := by simpa only [mem_ball, dist_zero_right] using hz
  let R' := (‖z‖ + R) / 2
  have hR' : 0 < R' := by dsimp [R']; positivity
  have hR'R : R' < R := by dsimp [R']; linarith
  have hz' : z ∈ ball 0 R' := by rw [mem_ball, dist_zero_right]; dsimp [R']; linarith
  obtain ⟨B, hB, hb⟩ := exists_bound_roots (isCompact_closedBall (0 : ℂ) R')
    (closedBall_subset_ball hR'R) hroots
  let radius := B + ‖s‖ + 2
  have hradius : 0 < radius := by dsimp [radius]; positivity
  let U := ball (0 : ℂ) R ×ˢ (univ : Set ℂ)
  let V := ball (0 : ℂ) R' ×ˢ ball s 1
  let den := movingRootProduct roots
  have hden : DifferentiableOn ℂ den U := differentiableOn_movingRootProduct hroots
  let v : ℂ × ℂ := (0, 1)
  let Q := circleDivision den F v radius
  have hshift (w : ℂ × ℂ) (x : ℂ) : w + x • v = (w.1, w.2 + x) := by
    ext <;> simp [v, smul_eq_mul]
  have hcircle (w : ℂ × ℂ) (hw : w ∈ V) (x : ℂ) (hx : x ∈ sphere 0 radius) :
      w + x • v ∈ U ∧ den (w + x • v) ≠ 0 := by
    rw [hshift]
    refine ⟨⟨ball_subset_ball hR'R.le hw.1, mem_univ _⟩, ?_⟩
    apply movingRootProduct_ne_zero
    intro r hr he
    have hrb := hb r hr w.1 (ball_subset_closedBall hw.1)
    have hw₂ := (norm_le_insert' w.2 s).trans_lt
      (add_lt_add_right (dist_eq_norm w.2 s ▸ mem_ball.mp hw.2) ‖s‖)
    have hx' : ‖x‖ = radius := by simpa only [mem_sphere, dist_zero_right] using hx
    have htri := norm_add_le (w.2 + x) (-w.2)
    rw [show w.2 + x + -w.2 = x by abel, norm_neg, he, hx'] at htri
    dsimp [radius] at htri
    linarith
  have hQ : DifferentiableOn ℂ Q V :=
    differentiableOn_circleDivision (isOpen_ball.prod isOpen_univ) hden hF v hradius hcircle
  refine ⟨R', hz', Q, hQ, ?_⟩
  rintro ⟨a, t⟩ hat
  have hmaps : MapsTo (fun b : ℂ => (b, t)) (ball 0 R') V := fun _ hb => ⟨hb, hat.2⟩
  have hMaps : MapsTo (fun b : ℂ => (b, t)) (ball 0 R') U :=
    fun _ hb => ⟨ball_subset_ball hR'R.le hb, mem_univ _⟩
  have hleft : DifferentiableOn ℂ (fun b : ℂ => F (b, t)) (ball 0 R') :=
    hF.comp (by fun_prop) hMaps
  have hright : DifferentiableOn ℂ (fun b : ℂ => den (b, t) * Q (b, t)) (ball 0 R') :=
    (hden.comp (by fun_prop) hMaps).mul (hQ.comp (by fun_prop) hmaps)
  apply (hleft.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_frequently_eq
    (hright.analyticOnNhd isOpen_ball) (convex_ball 0 R').isPreconnected (mem_ball_self hR') _ hat.1
  have hb' : ∀ᶠ b in 𝓝[≠] (0 : ℂ), b ∈ ball 0 R' :=
    nhdsWithin_le_nhds (ball_mem_nhds _ hR')
  refine (hquot.and_eventually hb').mono ?_
  rintro b ⟨⟨G, hG, heq⟩, hb⟩
  have havg : Q (b, t) = G t := by
    unfold Q circleDivision
    have htranslate : Differentiable ℂ (fun x : ℂ => t + x) := by fun_prop
    have hmean : Real.circleAverage (fun x : ℂ => G (t + x)) 0 radius = G (t + 0) :=
      ((hG.comp htranslate).differentiableOn.diffContOnCl).circleAverage
    rw [show G t = G (t + 0) by rw [add_zero], ← hmean]
    apply Real.circleAverage_congr_sphere
    intro x hx
    have hd := (hcircle (b, t) ⟨hb, hat.2⟩ x (by simpa [abs_of_pos hradius] using hx)).2
    change F ((b, t) + x • v) / den ((b, t) + x • v) = G (t + x)
    rw [hshift] at hd ⊢
    exact (div_eq_iff hd).2 ((heq (t + x)).trans (mul_comm _ _))
  rw [havg]
  exact heq t

/-- Joint holomorphic division on a parameter disk times the spectral plane.
It suffices that the full polynomial divides the entire spectral slice at
parameters accumulating to the center. -/
def MovingRootDivisionStatement : Prop :=
  ∀ (R : ℝ), 0 < R → ∀ (F : ℂ × ℂ → ℂ) (roots : List (ℂ → ℂ)),
    DifferentiableOn ℂ F (ball 0 R ×ˢ (univ : Set ℂ)) →
    (∀ r ∈ roots, DifferentiableOn ℂ r (ball 0 R)) →
    (∃ᶠ z in 𝓝[≠] (0 : ℂ), ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      ∀ s, F (z, s) = movingRootProduct roots (z, s) * G s) →
    ∃ Q : ℂ × ℂ → ℂ, DifferentiableOn ℂ Q (ball 0 R ×ˢ (univ : Set ℂ)) ∧
      ∀ w ∈ ball 0 R ×ˢ (univ : Set ℂ), F w = movingRootProduct roots w * Q w

theorem movingRootDivision : MovingRootDivisionStatement := by
  intro R hR F roots hF hroots hquot
  let Q (w : ℂ × ℂ) :=
    limUnder (𝓝[≠] w.2) (fun t => F (w.1, t) / movingRootProduct roots (w.1, t))
  have hlocal (z s : ℂ) (hz : z ∈ ball 0 R) :
      DifferentiableAt ℂ Q (z, s) ∧ F (z, s) = movingRootProduct roots (z, s) * Q (z, s) := by
    obtain ⟨R', hz', G, hG, heq⟩ := exists_local_quotient hR hF hroots hquot hz (s := s)
    let V := ball (0 : ℂ) R' ×ˢ ball s 1
    have hV : IsOpen V := isOpen_ball.prod isOpen_ball
    have hmem : (z, s) ∈ V := ⟨hz', mem_ball_self zero_lt_one⟩
    have hQG : EqOn Q G V := by
      intro w hw
      have hcont : ContinuousAt (fun t : ℂ => G (w.1, t)) w.2 :=
        ((hG.differentiableAt (hV.mem_nhds hw)).comp w.2
          (by fun_prop)).continuousAt
      have htend : Tendsto (fun t : ℂ => G (w.1, t)) (𝓝[≠] w.2) (𝓝 (G w)) :=
        hcont.tendsto.mono_left nhdsWithin_le_nhds
      have hraw :
          (fun t => F (w.1, t) / movingRootProduct roots (w.1, t)) =ᶠ[𝓝[≠] w.2]
            (fun t => G (w.1, t)) := by
        have ht' : ∀ᶠ t in 𝓝[≠] w.2, t ∈ ball s 1 :=
          nhdsWithin_le_nhds (isOpen_ball.mem_nhds hw.2)
        filter_upwards [movingRootProduct_eventually_ne_zero roots w.1 w.2, ht'] with t hden ht
        exact (div_eq_iff hden).2 ((heq (w.1, t) ⟨hw.1, ht⟩).trans (mul_comm _ _))
      exact ((tendsto_congr' hraw).2 htend).limUnder_eq
    refine ⟨(hG.differentiableAt (hV.mem_nhds hmem)).congr_of_eventuallyEq ?_, ?_⟩
    · have hV' : ∀ᶠ w in 𝓝 (z, s), w ∈ V := hV.mem_nhds hmem
      filter_upwards [hV'] with w hw
      exact hQG hw
    · simpa only [hQG hmem] using heq _ hmem
  exact ⟨Q, fun w hw => (hlocal w.1 w.2 hw.1).1.differentiableWithinAt,
    fun w hw => (hlocal w.1 w.2 hw.1).2⟩

end Langlands.Analysis.SeveralComplex
