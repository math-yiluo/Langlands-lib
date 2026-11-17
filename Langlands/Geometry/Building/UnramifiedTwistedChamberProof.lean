import Langlands.Geometry.Building.UnramifiedTwistedChamberReduction
import Langlands.Geometry.Building.UnramifiedBuildingMetricProof
import Langlands.Geometry.Building.UnramifiedTwistedChamberThroughFixedPointProof

/-! # Twisted-stable chambers over the maximal unramified extension -/

universe u

namespace Langlands.Geometry.Building

/-- Every finite-level cocycle admits a chamber stable under its twisted Galois action. -/
theorem unramifiedTwistedChamber : UnramifiedTwistedChamberStatement.{u} :=
  unramifiedTwistedChamber_of_metric unramifiedBuildingMetric
    unramifiedTwistedChamberThroughFixedPoint

end Langlands.Geometry.Building
