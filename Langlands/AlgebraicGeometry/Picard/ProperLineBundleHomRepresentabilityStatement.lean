import Langlands.AlgebraicGeometry.CoherentSheaves.IntrinsicModuleHomPresheaf
import Langlands.AlgebraicGeometry.Picard.Groupoid
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Affine representation of actual line-bundle Hom presheaves -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Proper flat line-bundle Hom representability on the entire scheme slice. -/
def ProperLineBundleHomRepresentabilityStatement : Prop :=
  ∀ (S X : Scheme.{u}) (f : X ⟶ S),
    IsProper f → Flat f → LocallyOfFinitePresentation f →
      ∀ (T : Over S) (L M : PicardGroupoid ((relativeSpace f).obj T)),
        ∃ H : Over T.left,
          Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj H ≅
            CoherentSheaves.intrinsicModuleHomPresheaf
              ((relativeProjection f).app T) L.of.obj M.of.obj) ∧
          IsAffineHom H.hom ∧ LocallyOfFinitePresentation H.hom

end Langlands.AlgebraicGeometry.Picard
