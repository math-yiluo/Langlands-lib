import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Reduced

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry

/-- Every smooth morphism has geometrically reduced fibres. -/
def SmoothGeometricallyReduced : Prop :=
  ∀ (X S : Scheme.{u}) (p : X ⟶ S), Smooth p → GeometricallyReduced p

end Langlands.AlgebraicGeometry
