import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Langlands.AlgebraicGeometry.Picard.GeometricallyUnibranchDomain

/-! # Birational unramified morphisms over geometrically unibranch bases -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- A separated, locally finite type, formally unramified birational morphism
between integral schemes is an open immersion if the base is geometrically
unibranch. This is the integral specialization of EGA IV 18.10.2(iii) followed
by 18.10.18; it defines the proposition without proving it. -/
def BirationalUnramifiedOpenImmersionStatement : Prop :=
  ∀ (S Z : Scheme.{u}) [IsIntegral S] [IsIntegral Z],
    GeometricallyUnibranchIntegralScheme S →
    ∀ (f : Z ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [FormallyUnramified f],
      Scheme.BirationalOver f (𝟙 S) → IsOpenImmersion f

end Langlands.AlgebraicGeometry
