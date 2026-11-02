import Langlands.AlgebraicGeometry.CoherentSheaves.HomPresheaf
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Affine representation of actual coherent-family morphisms -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.CoherentSheaves

/-- Proper-Hom representability for actual coherent families on the full slice. -/
def ProperHomRepresentabilityStatement : Prop :=
  ∀ (S X : Scheme.{u}) (f : X ⟶ S),
    IsProper f → LocallyOfFinitePresentation f →
      ∀ (T : Over S) (M N : FamilyGroupoid f T),
        ∃ H : Over T.left,
          Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj H ≅
            FamilyGroupoid.homPresheaf f M N) ∧
          IsAffineHom H.hom ∧ LocallyOfFinitePresentation H.hom

end Langlands.AlgebraicGeometry.CoherentSheaves
