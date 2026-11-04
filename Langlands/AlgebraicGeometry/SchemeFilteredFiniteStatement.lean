import Langlands.AlgebraicGeometry.SchemeFilteredRingTail
import Langlands.AlgebraicGeometry.SchemeLimitRelativeFiniteStatement

/-! # Finite-morphism descent over the actual filtered ring system -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

open AffineLimit

/-- Finite-morphism descent along the actual spectra of a filtered algebra diagram. -/
def SpectrumFiniteDescent : Prop :=
  ∀ (R : Type u) [CommRing R] {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} R) (c : Cocone F) (_hc : IsColimit c)
    (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
    [LocallyOfFiniteType f.left] [QuasiCompact f.left] [QuasiSeparated f.left]
    [QuasiCompact Y.hom],
      IsFinite (baseChangeMap X.hom Y.hom f.left (Over.w f)
        (spectrumBaseMap R F c)) ↔
      ∃ j : J, IsFinite (baseChangeMap X.hom Y.hom f.left (Over.w f)
        ((spectrumStructure R F).app (Opposite.op j)))

/-- The chosen initial stage and all subsequent ring maps are the original ones. -/
def InitialRingFiniteDescent : Prop :=
  ∀ {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (_hc : IsColimit c) (j₀ : J)
    (X Y : Over (Spec (F.obj j₀))) (f : X ⟶ Y)
    [LocallyOfFiniteType f.left] [QuasiCompact f.left] [QuasiSeparated f.left]
    [QuasiCompact Y.hom],
      IsFinite (baseChangeMap X.hom Y.hom f.left (Over.w f)
        (Spec.map (c.ι.app j₀))) ↔
      ∃ j : Under j₀, IsFinite
        (baseChangeMap X.hom Y.hom f.left (Over.w f) (Spec.map (F.map j.hom)))

/-- The source's finitely presented models imply the relative finiteness
hypotheses, rather than supplying them as additional assumptions. -/
def FinitePresentationInitialRingFiniteDescent : Prop :=
  ∀ {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (_hc : IsColimit c) (j₀ : J)
    (X Y : Over (Spec (F.obj j₀))) (f : X ⟶ Y)
    [LocallyOfFinitePresentation X.hom] [QuasiCompact X.hom] [QuasiSeparated X.hom]
    [LocallyOfFinitePresentation Y.hom] [QuasiCompact Y.hom] [QuasiSeparated Y.hom],
      IsFinite (baseChangeMap X.hom Y.hom f.left (Over.w f)
        (Spec.map (c.ι.app j₀))) ↔
      ∃ j : Under j₀, IsFinite
        (baseChangeMap X.hom Y.hom f.left (Over.w f) (Spec.map (F.map j.hom)))

/-- The spectrum, original initial-stage, and source finite-presentation
forms of relative finite-morphism descent. -/
def RingSystemFiniteDescent : Prop :=
  SpectrumFiniteDescent.{u} ∧ InitialRingFiniteDescent.{u} ∧
    FinitePresentationInitialRingFiniteDescent.{u}

end Langlands.AlgebraicGeometry.SchemeLimitModel
