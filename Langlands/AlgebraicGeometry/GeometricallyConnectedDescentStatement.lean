import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Surjective descent of geometric connectedness: proposition target -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Geometric connectedness can be tested after a surjective change of base.
This declaration is a proposition target. -/
def GeometricallyConnectedSurjectiveDescentStatement : Prop :=
  ∀ (X Y S : Scheme.{u}) (f : X ⟶ S) (g : Y ⟶ S),
    Surjective g → GeometricallyConnected (pullback.snd f g) →
      GeometricallyConnected f

end Langlands.AlgebraicGeometry
