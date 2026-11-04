import Langlands.AlgebraicGeometry.SchemeLimitModelSpectrum
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Actual relative model Hom comparison along filtered algebra diagrams -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

/-- The original algebra-index Hom quotient compares bijectively with actual
relative morphisms over the colimit algebra, with separate weaker hypotheses. -/
def SpectrumModelHomColimitComparison : Prop :=
  ∀ (R : Type u) [CommRing R] (J : Type u) [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} R) (c : Cocone F) (_hc : IsColimit c)
    (X Y : Over (Spec (CommRingCat.of R))),
    (QuasiCompact X.hom → LocallyOfFiniteType Y.hom →
      Function.Injective (spectrumHomColimitMap R F c X Y)) ∧
    (QuasiCompact X.hom → QuasiSeparated X.hom → LocallyOfFinitePresentation Y.hom →
      Function.Surjective (spectrumHomColimitMap R F c X Y)) ∧
    (QuasiCompact X.hom → QuasiSeparated X.hom → LocallyOfFinitePresentation Y.hom →
      Function.Bijective (spectrumHomColimitMap R F c X Y) ∧
        Nonempty (IsColimit (spectrumHomCocone R F c X Y)))

end Langlands.AlgebraicGeometry.SchemeLimitModel
