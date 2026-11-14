import Langlands.Geometry.Building.UnramifiedRetractionDistanceProof

/-! # Complete NPC metrics on actual maximal-unramified buildings -/

noncomputable section

universe u

namespace Langlands.Geometry.Building.MaximalUnramified

/-- Every supplied actual maximal-unramified building carries a complete NPC
metric for which its existing rational-point action is isometric. -/
theorem completeNPCMetric : CompleteNPCMetricStatement.{u} :=
  completeNPCMetricStatement_of_retractionDistance commonApartments retractionDistance

end Langlands.Geometry.Building.MaximalUnramified
