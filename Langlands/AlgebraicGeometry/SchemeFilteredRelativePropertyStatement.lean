import Langlands.AlgebraicGeometry.SchemeFilteredRingTail
import Langlands.AlgebraicGeometry.SchemeLimitRelativePropertyStatement

/-! # Relative smoothness and flatness over the original ring system -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

open AffineLimit

/-- Detection of a relative property on actual spectra of a filtered algebra
diagram, for a finitely presented morphism with quasi-compact target. -/
def SpectrumRelativePropertyDescent (P : MorphismProperty Scheme.{u}) : Prop :=
  ∀ (R : Type u) [CommRing R] {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} R) (c : Cocone F) (_hc : IsColimit c)
    (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
    [LocallyOfFinitePresentation f.left] [QuasiCompact f.left]
    [QuasiSeparated f.left] [QuasiCompact Y.hom],
      P (baseChangeMap X.hom Y.hom f.left (Over.w f)
        (spectrumBaseMap R F c)) ↔
      ∃ j : J, P (baseChangeMap X.hom Y.hom f.left (Over.w f)
        ((spectrumStructure R F).app (Opposite.op j)))

/-- The eventual stage includes an actual arrow out of the original
initial ring; neither the rings nor their transition maps are replaced. -/
def InitialRingRelativePropertyDescent (P : MorphismProperty Scheme.{u}) : Prop :=
  ∀ {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (_hc : IsColimit c) (j₀ : J)
    (X Y : Over (Spec (F.obj j₀))) (f : X ⟶ Y)
    [LocallyOfFinitePresentation f.left] [QuasiCompact f.left]
    [QuasiSeparated f.left] [QuasiCompact Y.hom],
      P (baseChangeMap X.hom Y.hom f.left (Over.w f)
        (Spec.map (c.ι.app j₀))) ↔
      ∃ j : Under j₀, P
        (baseChangeMap X.hom Y.hom f.left (Over.w f) (Spec.map (F.map j.hom)))

/-- The source's finitely presented models imply the relative hypotheses;
no extra finiteness assumption on their morphism is imposed. -/
def FinitePresentationInitialRingRelativePropertyDescent
    (P : MorphismProperty Scheme.{u}) : Prop :=
  ∀ {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (_hc : IsColimit c) (j₀ : J)
    (X Y : Over (Spec (F.obj j₀))) (f : X ⟶ Y)
    [LocallyOfFinitePresentation X.hom] [QuasiCompact X.hom] [QuasiSeparated X.hom]
    [LocallyOfFinitePresentation Y.hom] [QuasiCompact Y.hom] [QuasiSeparated Y.hom],
      P (baseChangeMap X.hom Y.hom f.left (Over.w f)
        (Spec.map (c.ι.app j₀))) ↔
      ∃ j : Under j₀, P
        (baseChangeMap X.hom Y.hom f.left (Over.w f) (Spec.map (F.map j.hom)))

/-- Both relative properties along actual filtered algebra spectra. -/
def SpectrumRelativeSmoothFlatDescent : Prop :=
  SpectrumRelativePropertyDescent.{u} @Smooth ∧
    SpectrumRelativePropertyDescent.{u} @Flat

/-- Both relative properties along actual original-ring transitions. -/
def InitialRingRelativeSmoothFlatDescent : Prop :=
  InitialRingRelativePropertyDescent.{u} @Smooth ∧
    InitialRingRelativePropertyDescent.{u} @Flat

/-- The smooth and flat clauses for the source's finitely presented models. -/
def FinitePresentationInitialRingRelativeSmoothFlatDescent : Prop :=
  FinitePresentationInitialRingRelativePropertyDescent.{u} @Smooth ∧
    FinitePresentationInitialRingRelativePropertyDescent.{u} @Flat

/-- The spectrum, initial-stage and source finite-presentation forms. -/
def RingSystemRelativeSmoothFlatDescent : Prop :=
  SpectrumRelativeSmoothFlatDescent.{u} ∧ InitialRingRelativeSmoothFlatDescent.{u} ∧
    FinitePresentationInitialRingRelativeSmoothFlatDescent.{u}

end Langlands.AlgebraicGeometry.SchemeLimitModel
