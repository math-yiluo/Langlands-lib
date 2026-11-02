import Langlands.Geometry.Metric.KPClosedBallConvexityProof

/-! # The closed bounded geodesic convex hull -/

open Set Bornology unitInterval

namespace Langlands.Geometry.Metric.KP

universe uX

/-- The assertion following corrected KP Definition 1.1.14, with all four clauses. -/
theorem closedConvexHull : ClosedConvexHullStatement.{uX} := by
  intro X _ hX hgeo M hne hb
  obtain ⟨z, hz⟩ := hne
  obtain ⟨r, hsub⟩ := (Metric.isBounded_iff_subset_closedBall z).mp hb
  have hr : 0 ≤ r := by
    have := hsub hz
    simpa using this
  have hball : IsGeodesicallyConvex (Metric.closedBall z r) :=
    closedBallConvexity X hX hgeo z r hr
  refine ⟨isClosed_closedGeodesicConvexHull M, ?_,
    isGeodesicallyConvex_closedGeodesicConvexHull ⟨z, hz⟩,
    subset_closedGeodesicConvexHull M⟩
  exact isBounded_closedGeodesicConvexHull
    ⟨Metric.closedBall z r, Metric.isClosed_closedBall,
      Metric.isBounded_closedBall, hball, hsub⟩

end Langlands.Geometry.Metric.KP
