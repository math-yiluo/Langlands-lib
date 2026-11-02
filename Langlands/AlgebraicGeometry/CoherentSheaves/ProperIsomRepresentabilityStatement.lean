import Langlands.AlgebraicGeometry.CoherentSheaves.IsomPresheaf
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Affine representation of actual coherent-family isomorphisms -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.CoherentSheaves

/-- For a proper locally finitely presented ambient morphism, the actual
full-slice Isom presheaf of any two coherent families is represented by an
affine scheme locally of finite presentation over its test base. -/
def ProperIsomRepresentabilityStatement : Prop :=
  ∀ (S X : Scheme.{u}) (f : X ⟶ S),
    IsProper f → LocallyOfFinitePresentation f →
      ∀ (T : Over S) (M N : FamilyGroupoid f T),
        ∃ I : Over T.left,
          Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj I ≅
            FamilyGroupoid.isomPresheaf f M N) ∧
          IsAffineHom I.hom ∧ LocallyOfFinitePresentation I.hom

end Langlands.AlgebraicGeometry.CoherentSheaves
