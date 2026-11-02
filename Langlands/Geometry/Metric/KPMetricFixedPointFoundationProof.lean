import Langlands.Geometry.Metric.KPGeodesicUniquenessProof
import Langlands.Geometry.Metric.KPClosedBallConvexityProof
import Langlands.Geometry.Metric.KPClosedConvexHullProof
import Langlands.Geometry.Metric.KPBarycenterProof
import Langlands.Geometry.Metric.KPBoundedSetStabilizerProof
import Langlands.Geometry.Metric.KPBoundedActionFixedPointProof

/-! # The aggregate Kaletha–Prasad metric fixed-point foundation -/

namespace Langlands.Geometry.Metric.KP

universe uX uG

/-- The conjunction of KP Lemmas 1.1.11 and 1.1.13, the hull assertion after Definition 1.1.14,
Theorem 1.1.15 and Corollary 1.1.19, assembled from the six component proofs. -/
theorem metricFixedPointFoundation : MetricFixedPointFoundationStatement.{uX, uG} :=
  ⟨geodesicUniqueness, closedBallConvexity, closedConvexHull, barycenter,
    boundedSetStabilizerFixedPoint, boundedActionFixedPoint⟩

end Langlands.Geometry.Metric.KP
