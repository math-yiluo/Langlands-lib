import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Stalk

/-! # Local algebra and closed immersion near a singleton finite fiber -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- A finite map with a singleton fiber has a finite actual stalk map there;
surjectivity of that stalk map spreads to a whole target-open restriction. -/
def FiniteSingletonFiberLocalClosedImmersionStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [IsFinite f] (x : X),
    f ⁻¹' {f x} = {x} →
    (f.stalkMap x).hom.Finite ∧
      (Function.Surjective (f.stalkMap x).hom →
        ∃ V : Y.Opens, f x ∈ V ∧ IsClosedImmersion (f ∣_ V))

end Langlands.AlgebraicGeometry
