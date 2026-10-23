import Langlands.Algebra.EssFinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Essential finite presentation of scheme stalk maps -/

universe u

open CategoryTheory

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry

/-- A locally finitely presented scheme morphism induces an essentially finitely presented
algebra on each stalk, using the algebra structure of its actual stalk map.
This is a derived consequence of affine local finite presentation and Stacks tag 00QM.
It is a proposition to be proved, not a proof of that consequence. -/
def StalkEssFinitePresentationStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (x : X),
    LocallyOfFinitePresentation f →
      letI := (f.stalkMap x).hom.toAlgebra
      Langlands.Algebra.EssFinitePresentation
        (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

end Langlands.AlgebraicGeometry
