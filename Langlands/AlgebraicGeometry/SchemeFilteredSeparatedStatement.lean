import Langlands.AlgebraicGeometry.SchemeFilteredRingTail
import Langlands.AlgebraicGeometry.SchemeLimitSeparatedStatement

/-! # Relative separatedness over the actual filtered ring system -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

open AffineLimit

/-- Separatedness descent along the actual spectra of a filtered algebra diagram. -/
def SpectrumSeparatednessDescent : Prop :=
  ∀ (R : Type u) [CommRing R] {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} R) (c : Cocone F) (_hc : IsColimit c)
    (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
    [QuasiCompact f.left] [QuasiSeparated f.left] [QuasiCompact X.hom],
      IsSeparated (baseChangeMap X.hom Y.hom f.left (Over.w f)
        (spectrumBaseMap R F c)) ↔
      ∃ j : J, IsSeparated (baseChangeMap X.hom Y.hom f.left (Over.w f)
        ((spectrumStructure R F).app (Opposite.op j)))

/-- The chosen initial stage and all subsequent ring maps are the original ones. -/
def InitialRingSeparatednessDescent : Prop :=
  ∀ {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (_hc : IsColimit c) (j₀ : J)
    (X Y : Over (Spec (F.obj j₀))) (f : X ⟶ Y)
    [QuasiCompact f.left] [QuasiSeparated f.left] [QuasiCompact X.hom],
      IsSeparated (baseChangeMap X.hom Y.hom f.left (Over.w f)
        (Spec.map (c.ι.app j₀))) ↔
      ∃ j : Under j₀, IsSeparated
        (baseChangeMap X.hom Y.hom f.left (Over.w f) (Spec.map (F.map j.hom)))

/-- The source's finitely presented models imply the relative finiteness
hypotheses, rather than supplying them as additional assumptions. -/
def FinitePresentationInitialRingSeparatednessDescent : Prop :=
  ∀ {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (_hc : IsColimit c) (j₀ : J)
    (X Y : Over (Spec (F.obj j₀))) (f : X ⟶ Y)
    [LocallyOfFinitePresentation X.hom] [QuasiCompact X.hom] [QuasiSeparated X.hom]
    [LocallyOfFinitePresentation Y.hom] [QuasiCompact Y.hom] [QuasiSeparated Y.hom],
      IsSeparated (baseChangeMap X.hom Y.hom f.left (Over.w f)
        (Spec.map (c.ι.app j₀))) ↔
      ∃ j : Under j₀, IsSeparated
        (baseChangeMap X.hom Y.hom f.left (Over.w f) (Spec.map (F.map j.hom)))

/-- The spectrum, original initial-stage, and source finite-presentation
forms of relative separatedness descent. -/
def RingSystemSeparatednessDescent : Prop :=
  SpectrumSeparatednessDescent.{u} ∧ InitialRingSeparatednessDescent.{u} ∧
    FinitePresentationInitialRingSeparatednessDescent.{u}

end Langlands.AlgebraicGeometry.SchemeLimitModel
