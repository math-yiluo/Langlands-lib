import Langlands.Geometry.Building.UnramifiedTorusUnitFiniteOrbitReduction
import Langlands.Geometry.Building.UnramifiedSemilinearMetricActionProof

/-! # A simultaneous Galois and torus-unit fixed point over the maximal unramified extension -/

universe u

namespace Langlands.Geometry.Building

/-- A connected reductive group over a nonarchimedean local field has building
data over the maximal unramified extension with a semilinear Galois action and
a point fixed by both Galois and the bounded points of the given split torus. -/
theorem unramifiedTorusUnitGaloisFixedPoint :
    UnramifiedTorusUnitGaloisFixedPointStatement.{u} :=
  unramifiedTorusUnitGaloisFixedPoint_of_metricAction unramifiedSemilinearMetricAction

end Langlands.Geometry.Building
