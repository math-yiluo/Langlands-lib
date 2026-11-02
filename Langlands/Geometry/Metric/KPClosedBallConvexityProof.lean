import Langlands.Geometry.Metric.KPGeodesicUniquenessProof
import Mathlib.Topology.Order.Compact

/-! # Closed balls in an NPC geodesic space are convex -/

open Set Bornology unitInterval

namespace Langlands.Geometry.Metric.KP

universe uX

variable {X : Type*} [MetricSpace X]

/-- A geodesic stays within the larger of the endpoint distances from a fixed point. -/
theorem IsGeodesic.dist_le_max_endpoints (hX : IsNonpositivelyCurved X)
    {x y : X} {γ : Path x y} (hγ : IsGeodesic γ) (z : X) (s : I) :
    dist (γ s) z ≤ max (dist x z) (dist y z) := by
  rcases eq_or_ne x y with rfl | hxy
  · rw [hγ.eq_refl]
    simp
  have hL : 0 < dist x y := dist_pos.mpr hxy
  obtain ⟨t, _, ht⟩ := isCompact_univ.exists_isMaxOn (univ_nonempty : (univ : Set I).Nonempty)
    (γ.continuous.dist continuous_const).continuousOn
  have hmax : dist (γ t) z ≤ max (dist x z) (dist y z) := by
    by_cases ht0 : t = 0
    · simp [ht0]
    by_cases ht1 : t = 1
    · simp [ht1]
    have htpos : 0 < (t : ℝ) := by
      have hne : (t : ℝ) ≠ 0 := fun h => ht0 (Subtype.ext h)
      exact lt_of_le_of_ne (nonneg t) (Ne.symm hne)
    have htlt : (t : ℝ) < 1 := by
      have hne : (t : ℝ) ≠ 1 := fun h => ht1 (Subtype.ext h)
      exact lt_of_le_of_ne (le_one t) hne
    let ε : ℝ := min (t : ℝ) (1 - t)
    have hε : 0 < ε := lt_min htpos (sub_pos.mpr htlt)
    have hεt : ε ≤ t := min_le_left _ _
    have hε1 : ε ≤ 1 - t := min_le_right _ _
    let a : I := ⟨t - ε, by constructor <;> linarith⟩
    let b : I := ⟨t + ε, by constructor <;> linarith⟩
    have hmidparam : Set.Icc.convexComb a b
        ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩ = t := by
      apply Subtype.ext
      simp only [Set.Icc.coe_convexComb]
      change (1 - (1 / 2 : ℝ)) * ((t : ℝ) - ε) + (1 / 2 : ℝ) * (t + ε) = t
      ring
    have hm := (hγ.subpath a b).isNPCMidpoint hX
    change IsNPCMidpoint (γ a) (γ b) (γ (Set.Icc.convexComb a b
      ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩)) at hm
    rw [hmidparam] at hm
    have hineq := hm z
    have ha : dist (γ a) z ^ 2 ≤ dist (γ t) z ^ 2 :=
      (sq_le_sq₀ dist_nonneg dist_nonneg).mpr (ht (mem_univ a))
    have hb : dist (γ b) z ^ 2 ≤ dist (γ t) z ^ 2 :=
      (sq_le_sq₀ dist_nonneg dist_nonneg).mpr (ht (mem_univ b))
    have hzero : dist (γ a) (γ b) = 0 := by
      nlinarith [sq_nonneg (dist (γ a) (γ b)),
        dist_nonneg (x := γ a) (y := γ b)]
    have hdist := hγ a b
    rw [hzero] at hdist
    have hab : |(a : ℝ) - b| = 0 := (mul_eq_zero.mp hdist.symm).resolve_left (ne_of_gt hL)
    have heq := abs_eq_zero.mp hab
    change (t : ℝ) - ε - (t + ε) = 0 at heq
    linarith
  exact (ht (mem_univ s)).trans hmax

/-- Corrected KP Lemma 1.1.13, including radius zero and nonempty convexity. -/
theorem closedBallConvexity : ClosedBallConvexityStatement.{uX} := by
  intro X _ hX _ z r hr
  refine ⟨⟨z, by simpa using hr⟩, ?_⟩
  intro x hx y hy γ hγ p hp
  obtain ⟨t, rfl⟩ := hp
  have hx' : dist x z ≤ r := hx
  have hy' : dist y z ≤ r := hy
  exact (hγ.dist_le_max_endpoints hX z t).trans (max_le hx' hy')

end Langlands.Geometry.Metric.KP
