import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Smooth and flat models over actual filtered ring stages -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

/-- A finitely presented scheme with property `P` over a filtered ring
colimit admits a finitely presented model with `P` at an actual stage. -/
def SchemeFilteredPropertyModelExistence (P : MorphismProperty Scheme.{u}) : Prop :=
  ∀ (J : Type u) [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (_hc : IsColimit c)
    (X : Scheme.{u}) (g : X ⟶ Spec c.pt)
    [QuasiCompact g] [QuasiSeparated g] [LocallyOfFinitePresentation g],
    P g →
    ∃ (j : J) (Xj : Scheme.{u}) (gj : Xj ⟶ Spec (F.obj j)) (π : X ⟶ Xj),
      LocallyOfFinitePresentation gj ∧ QuasiCompact gj ∧ QuasiSeparated gj ∧
        P gj ∧ IsPullback π g gj (Spec.map (c.ι.app j))

/-- Smooth finitely presented schemes admit smooth finitely presented models. -/
def SchemeFilteredSmoothModelExistence : Prop :=
  SchemeFilteredPropertyModelExistence.{u} @Smooth

/-- Flat finitely presented schemes admit flat finitely presented models. -/
def SchemeFilteredFlatModelExistence : Prop :=
  SchemeFilteredPropertyModelExistence.{u} @Flat

/-- The two structural model-existence assertions. -/
def SchemeFilteredSmoothFlatModelExistence : Prop :=
  SchemeFilteredSmoothModelExistence.{u} ∧ SchemeFilteredFlatModelExistence.{u}

end Langlands.AlgebraicGeometry.SchemeLimitModel
