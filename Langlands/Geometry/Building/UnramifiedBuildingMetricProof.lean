import Langlands.Geometry.Building.UnramifiedBuildingMetricReduction
import Langlands.Geometry.Building.IntegerValuationCommonApartmentsProof
import Langlands.Geometry.Building.UnramifiedRetractionDistanceProof

/-! # The complete invariant NPC metric on the maximal-unramified building

The published reduction `unramifiedBuildingMetricReduction` derives
`UnramifiedBuildingMetricStatement` from the common-apartment statement and the
retraction-distance statement; both premises are published theorems.
-/

universe u

namespace Langlands.Geometry.Building

/-- **KP Section 4.2 over the maximal unramified extension.** For a connected reductive
group `G` over a nonarchimedean local field `F`, a torus `T` whose base change is a
maximal split torus over `K = inertiaFixedField F`, and Galois-stable,
`ω`-compatible apartment and centralizer data, the reduced building of the descended
semilinear datum carries a complete nonpositively curved metric for which `G(K)` and
the coefficient action of `Aut(K/F)` act by isometries. -/
theorem unramifiedBuildingMetric : UnramifiedBuildingMetricStatement.{u} :=
  unramifiedBuildingMetricReduction MaximalUnramified.commonApartments
    MaximalUnramified.retractionDistance

end Langlands.Geometry.Building
