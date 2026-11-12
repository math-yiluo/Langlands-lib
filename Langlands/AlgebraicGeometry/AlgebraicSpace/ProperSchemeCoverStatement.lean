import Langlands.AlgebraicGeometry.AlgebraicSpace.ConnectedStructuralFibres
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Proper finitely presented algebraic spaces admit proper scheme covers -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- A proper finitely presented algebraic space over an affine base admits a
surjective cover by a scheme proper and locally finitely presented over that base.
This is the finite-presentation refinement of the weak Chow-cover consequence. -/
def ProperSchemeCoverStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsAffine S] (X : AlgebraicSpace S),
    IsQuasiSeparated X →
    HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X →
    IsProperMorphism (structuralMorphism X) →
    ∃ (U : Over S) (a : (schemeYoneda S).obj U ⟶ X.presheaf),
      IsSurjective a ∧ _root_.AlgebraicGeometry.IsProper U.hom ∧
        LocallyOfFinitePresentation U.hom

end Langlands.AlgebraicGeometry.AlgebraicSpace
