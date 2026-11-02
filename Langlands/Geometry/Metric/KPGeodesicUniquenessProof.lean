import Langlands.Geometry.Metric.KPFixedPointStatement

/-! # Unique geodesics and NPC midpoints -/

open Set Bornology unitInterval

namespace Langlands.Geometry.Metric.KP

universe uX

variable {X : Type*} [MetricSpace X]

/-- The NPC inequality identifies its point with the midpoint of any geodesic. -/
theorem IsNPCMidpoint.eq_geodesic_midpoint {x y m : X} (hm : IsNPCMidpoint x y m)
    {γ : Path x y} (hγ : IsGeodesic γ) :
    m = γ ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩ := by
  let t : I := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
  have hleft := hγ.dist_source t
  have hright := hγ.dist_target t
  have hineq := hm (γ t)
  rw [dist_comm y (γ t)] at hineq
  change dist x (γ t) = (1 / 2 : ℝ) * dist x y at hleft
  change dist (γ t) y = (1 - (1 / 2 : ℝ)) * dist x y at hright
  rw [hleft, hright] at hineq
  apply dist_eq_zero.mp
  nlinarith [sq_nonneg (dist m (γ t)), dist_nonneg (x := m) (y := γ t)]

/-- Every geodesic midpoint satisfies the primitive NPC inequality. -/
theorem IsGeodesic.isNPCMidpoint (hX : IsNonpositivelyCurved X) {x y : X}
    {γ : Path x y} (hγ : IsGeodesic γ) :
    IsNPCMidpoint x y (γ ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩) := by
  obtain ⟨m, hm⟩ := hX x y
  rwa [hm.eq_geodesic_midpoint hγ] at hm

/-- In an NPC space a point of a metric segment is determined by its two endpoint distances. -/
theorem eq_of_dist_eq_of_dist_add_eq (hX : IsNonpositivelyCurved X) {x y p q : X}
    (hleft : dist x p = dist x q) (hright : dist p y = dist q y)
    (hsum : dist x p + dist p y = dist x y) : p = q := by
  obtain ⟨m, hm⟩ := hX p q
  have hx := hm x
  have hy := hm y
  rw [dist_comm p x, dist_comm q x, dist_comm m x, ← hleft] at hx
  rw [← hright] at hy
  have hxle : dist x m ≤ dist x p := by
    nlinarith [sq_nonneg (dist p q), dist_nonneg (x := x) (y := m),
      dist_nonneg (x := x) (y := p)]
  have hyle : dist m y ≤ dist p y := by
    nlinarith [sq_nonneg (dist p q), dist_nonneg (x := m) (y := y),
      dist_nonneg (x := p) (y := y)]
  have htriangle := dist_triangle x m y
  have hxeq : dist x m = dist x p := by linarith
  rw [hxeq] at hx
  apply dist_eq_zero.mp
  nlinarith [sq_nonneg (dist p q), dist_nonneg (x := p) (y := q)]

/-- The constant-speed distance law and primitive NPC imply uniqueness of paths. -/
theorem IsGeodesic.eq_of_isNonpositivelyCurved (hX : IsNonpositivelyCurved X)
    {x y : X} {γ δ : Path x y} (hγ : IsGeodesic γ) (hδ : IsGeodesic δ) : γ = δ := by
  ext t
  apply eq_of_dist_eq_of_dist_add_eq hX (x := x) (y := y)
  · rw [hγ.dist_source, hδ.dist_source]
  · rw [hγ.dist_target, hδ.dist_target]
  · rw [hγ.dist_source, hγ.dist_target]
    ring

/-- KP Lemma 1.1.11, with the exact published universe-polymorphic target. -/
theorem geodesicUniqueness : GeodesicUniquenessStatement.{uX} := by
  intro X _ hX hgeo
  constructor
  · exact isUniquelyGeodesicSpace_iff.mpr
      ⟨hgeo, fun _ _ _ _ hγ hδ => hγ.eq_of_isNonpositivelyCurved hX hδ⟩
  · intro x y γ hγ m
    constructor
    · exact fun hm => hm.eq_geodesic_midpoint hγ
    · intro hm
      rw [hm]
      exact hγ.isNPCMidpoint hX

end Langlands.Geometry.Metric.KP
