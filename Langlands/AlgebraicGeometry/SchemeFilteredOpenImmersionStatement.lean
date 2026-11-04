import Langlands.AlgebraicGeometry.SchemeFilteredRingTail
import Langlands.AlgebraicGeometry.SchemeLimitOpenImmersionStatement

/-! # Relative open-immersion descent over the actual filtered ring system -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

open AffineLimit

/-- OpenImmersion descent along the actual spectra of a filtered algebra diagram. -/
def SpectrumOpenImmersionDescent : Prop :=
  ∀ (R : Type u) [CommRing R] {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} R) (c : Cocone F) (_hc : IsColimit c)
    (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
    [LocallyOfFinitePresentation X.hom] [QuasiCompact X.hom]
    [LocallyOfFinitePresentation Y.hom] [QuasiSeparated Y.hom],
      IsOpenImmersion (baseChangeMap X.hom Y.hom f.left (Over.w f)
        (spectrumBaseMap R F c)) ↔
      ∃ j : J, IsOpenImmersion (baseChangeMap X.hom Y.hom f.left (Over.w f)
        ((spectrumStructure R F).app (Opposite.op j)))

/-- The chosen initial stage and all subsequent ring maps are the original ones. -/
def InitialRingOpenImmersionDescent : Prop :=
  ∀ {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (_hc : IsColimit c) (j₀ : J)
    (X Y : Over (Spec (F.obj j₀))) (f : X ⟶ Y)
    [LocallyOfFinitePresentation X.hom] [QuasiCompact X.hom]
    [LocallyOfFinitePresentation Y.hom] [QuasiSeparated Y.hom],
      IsOpenImmersion (baseChangeMap X.hom Y.hom f.left (Over.w f)
        (Spec.map (c.ι.app j₀))) ↔
      ∃ j : Under j₀, IsOpenImmersion
        (baseChangeMap X.hom Y.hom f.left (Over.w f) (Spec.map (F.map j.hom)))

/-- The original source form retains finite presentation of both models. -/
def FinitePresentationInitialRingOpenImmersionDescent : Prop :=
  ∀ {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (_hc : IsColimit c) (j₀ : J)
    (X Y : Over (Spec (F.obj j₀))) (f : X ⟶ Y)
    [LocallyOfFinitePresentation X.hom] [QuasiCompact X.hom] [QuasiSeparated X.hom]
    [LocallyOfFinitePresentation Y.hom] [QuasiCompact Y.hom] [QuasiSeparated Y.hom],
      IsOpenImmersion (baseChangeMap X.hom Y.hom f.left (Over.w f)
        (Spec.map (c.ι.app j₀))) ↔
      ∃ j : Under j₀, IsOpenImmersion
        (baseChangeMap X.hom Y.hom f.left (Over.w f) (Spec.map (F.map j.hom)))

/-- The spectrum, original initial-stage, and source finite-presentation
forms of relative open-immersion descent. -/
def RingSystemOpenImmersionDescent : Prop :=
  SpectrumOpenImmersionDescent.{u} ∧ InitialRingOpenImmersionDescent.{u} ∧
    FinitePresentationInitialRingOpenImmersionDescent.{u}

end Langlands.AlgebraicGeometry.SchemeLimitModel
