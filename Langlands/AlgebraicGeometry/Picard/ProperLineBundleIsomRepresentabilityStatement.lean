import Langlands.AlgebraicGeometry.Picard.StackAtlas
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Affine representation of actual line-bundle isomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

namespace PicardGroupoid

variable {S X : Scheme.{u}} (f : X ⟶ S) {T : Over S}

/-- Actual isomorphisms between two line-bundle families, with ordinary
pullback and its coherent restrictions on the entire test slice. -/
def relativeIsomPresheaf
    (L M : PicardGroupoid ((relativeSpace f).obj T)) :
    AlgebraicSpace.Presheaf T.left :=
  (T.iteratedSliceBackward.op ⋙ (relative f).presheafHom L M) ⋙
    uliftFunctor.{u + 1}

end PicardGroupoid

/-- For a proper flat locally finitely presented ambient morphism, the
full-slice Isom presheaf of any two actual line-bundle families has an
affine scheme representative locally of finite presentation. -/
def ProperLineBundleIsomRepresentabilityStatement : Prop :=
  ∀ (S X : Scheme.{u}) (f : X ⟶ S),
    IsProper f → Flat f → LocallyOfFinitePresentation f →
      ∀ (T : Over S)
        (L M : PicardGroupoid ((relativeSpace f).obj T)),
        ∃ I : Over T.left,
          Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj I ≅
            PicardGroupoid.relativeIsomPresheaf f L M) ∧
          IsAffineHom I.hom ∧ LocallyOfFinitePresentation I.hom

end Langlands.AlgebraicGeometry.Picard
