import Langlands.AlgebraicGeometry.Picard.GeometricallyUnibranchDomain
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Dominant unramified morphisms over geometrically unibranch integral bases -/

universe u

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

namespace Langlands.AlgebraicGeometry

/-- Integral-source dominant specialization of Stacks Project tag 0GS8.
This declaration states the proposition; it supplies no proof of it. -/
def DominantUnramifiedEtaleStatement : Prop :=
  ∀ (X Y : Scheme.{u}) [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y),
    GeometricallyUnibranchIntegralScheme Y →
      LocallyOfFiniteType f → FormallyUnramified f → IsDominant f → Etale f

end Langlands.AlgebraicGeometry
