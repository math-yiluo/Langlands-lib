import Langlands.AlgebraicGeometry.SmoothGeometricallyReduced
import Langlands.AlgebraicGeometry.SmoothReducedProof

universe u

namespace Langlands.AlgebraicGeometry

/-- Every smooth morphism has geometrically reduced fibres. -/
theorem smoothGeometricallyReduced : SmoothGeometricallyReduced.{u} := by
  intro X S p hp
  exact @SmoothReducedProof.geometricallyReduced_of_smooth X S p hp

end Langlands.AlgebraicGeometry
