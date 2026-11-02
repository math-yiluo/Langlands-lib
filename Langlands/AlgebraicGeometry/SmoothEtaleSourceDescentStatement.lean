import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smoothness descends along a surjective etale map on the source -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Source descent of smoothness for actual schemes along a surjective etale
morphism. The composite is smooth over the original target scheme. -/
def SmoothEtaleSourceDescentStatement : Prop :=
  ∀ (W X S : Scheme.{u}) (p : W ⟶ X) (g : X ⟶ S),
    Etale p → Surjective p → Smooth (p ≫ g) → Smooth g

end Langlands.AlgebraicGeometry
