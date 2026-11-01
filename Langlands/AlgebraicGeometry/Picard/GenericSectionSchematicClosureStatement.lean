import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! # Integral birational closure of a generic section -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- The schematic image of a generic section is integral and birational to
the integral base, for a locally finite type formally unramified morphism. -/
def GenericSectionSchematicClosureStatement : Prop :=
  ∀ (S X : Scheme.{u}) [IsIntegral S] (p : X ⟶ S)
    [LocallyOfFiniteType p] [FormallyUnramified p]
    (a : Spec S.functionField ⟶ X),
    a ≫ p = S.fromSpecStalk (genericPoint S) →
    IsIntegral a.image ∧ Scheme.BirationalOver (a.imageι ≫ p) (𝟙 S)

end Langlands.AlgebraicGeometry
