import Langlands.AlgebraicGeometry.Picard.SmoothFamilyAlgebraicTriviality

/-! # Pullback preservation of smooth-family algebraic triviality -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- The actual relative rigidified pullback preserves the geometric-fibre
smooth-family condition. -/
def SmoothFamilyPullbackStatement : Prop :=
  ∀ (S : Scheme.{u}) (A : AbelianScheme S) (T U : Over S) (h : T ⟶ U)
    (L : RigidifiedFamily A U),
    IsAlgebraicallyTrivialFamilyViaSmoothFamily A L →
      IsAlgebraicallyTrivialFamilyViaSmoothFamily A
        ((RigidifiedLineBundle.relativePullback A.X.hom
          (unitSection A) (unitSection_comp A) h).obj L)

end Langlands.AbelianScheme
