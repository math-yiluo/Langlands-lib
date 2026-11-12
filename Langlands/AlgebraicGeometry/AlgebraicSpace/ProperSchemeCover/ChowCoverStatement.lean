import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry
import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # The weak Chow cover of a separated algebraic space of finite type

The interface between the scheme-cover construction (a weak form of Chow's lemma,
Stacks 089I) and its finite-presentation refinement.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover

/-- A separated algebraic space over an affine base, with a quasi-compact locally finitely
presented atlas, is the target of a surjective morphism from a scheme of finite type over the
base, every base change of which to a scheme is proper. -/
def ChowCoverStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsAffine S] (X : AlgebraicSpace S),
    IsSeparated X →
    HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X →
    ∃ (U : Over S) (a : (schemeYoneda S).obj U ⟶ X.presheaf),
      IsSurjective a ∧
        (MorphismProperty.inverseImage @_root_.AlgebraicGeometry.IsProper
          (Over.forget S)).relative (schemeYoneda S) a ∧
        LocallyOfFiniteType U.hom ∧ QuasiCompact U.hom

end Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover
