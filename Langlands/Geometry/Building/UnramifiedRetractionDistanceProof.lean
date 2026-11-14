import Langlands.Geometry.Building.IntegerValuationRetractionDistance
import Langlands.Geometry.Building.UnramifiedBuildingMetricReduction

/-! # The retraction distance on the maximal-unramified building

The generic construction is in `IntegerValuationRetractionDistance`.
-/

noncomputable section

universe u

namespace Langlands.Geometry.Building

namespace MaximalUnramified

/-- **Building distance with apartment retractions over `K`.** -/
theorem retractionDistance : RetractionDistanceStatement.{u} := by
  intro F _ _ _ _ H _ B
  exact B.exists_retractionDistance (exists_order_eq_one F)

end MaximalUnramified

end Langlands.Geometry.Building
