import Langlands.AlgebraicGeometry.SchemeFilteredPropertyModelStatement
import Langlands.AlgebraicGeometry.SchemeFilteredRingTail

/-! # Eventual smoothness and flatness of prescribed filtered-ring models -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

/-- The structural property of a prescribed finitely presented model over
an initial stage holds over the colimit exactly when it holds after an
actual outgoing original ring transition. -/
def InitialRingModelPropertyDescent (P : MorphismProperty Scheme.{u}) : Prop :=
  ∀ {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (_hc : IsColimit c)
    (j₀ : J) (X : Over (Spec (F.obj j₀)))
    [QuasiCompact X.hom] [QuasiSeparated X.hom] [LocallyOfFinitePresentation X.hom],
    P (pullback.fst (Spec.map (c.ι.app j₀)) X.hom) ↔
      ∃ j : Under j₀, P (pullback.fst (Spec.map (F.map j.hom)) X.hom)

/-- Smoothness of a prescribed finitely presented original-ring model descends. -/
def InitialRingModelSmoothDescent : Prop :=
  InitialRingModelPropertyDescent.{u} @Smooth

/-- Flatness of a prescribed finitely presented original-ring model descends. -/
def InitialRingModelFlatDescent : Prop :=
  InitialRingModelPropertyDescent.{u} @Flat

/-- Both structural properties descend for prescribed finitely presented models. -/
def InitialRingModelSmoothFlatDescent : Prop :=
  InitialRingModelSmoothDescent.{u} ∧ InitialRingModelFlatDescent.{u}

end Langlands.AlgebraicGeometry.SchemeLimitModel
