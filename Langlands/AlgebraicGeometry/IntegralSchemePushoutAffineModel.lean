import Langlands.AlgebraicGeometry.AffineSchemePushoutProof
import Langlands.AlgebraicGeometry.IntegralSchemePushoutAffineProperties

/-! # Affine models for spans of affine schemes -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry.IntegralSchemePushout.AffineSpan

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (i : Z ⟶ X) (j : Z ⟶ Y)

/-- The spectrum of the compatible-pair ring of global sections. -/
def model : Scheme.{u} := Spec (.of (i.appTop.hom.pullback j.appTop.hom))

instance : IsAffine (model i j) := inferInstanceAs (IsAffine (Spec _))

/-- The left cocone map, transported from the spectrum of global sections. -/
def inl : X ⟶ model i j :=
  X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (i.appTop.hom.pullbackFst j.appTop.hom))

/-- The right cocone map, transported from the spectrum of global sections. -/
def inr : Y ⟶ model i j :=
  Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (i.appTop.hom.pullbackSnd j.appTop.hom))

/-- A closed first leg supplies a pushout in locally ringed spaces. -/
lemma isPushout [IsClosedImmersion i] :
    IsPushout i.toLRSHom j.toLRSHom (inl i j).toLRSHom (inr i j).toLRSHom := by
  have h := AffineSchemePushout.isPushout_specLocallyRingedSpaceMap_canonical
    i.appTop j.appTop (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
  apply h.of_iso' (Scheme.forgetToLocallyRingedSpace.mapIso Z.isoSpec)
    (Scheme.forgetToLocallyRingedSpace.mapIso X.isoSpec)
    (Scheme.forgetToLocallyRingedSpace.mapIso Y.isoSpec) (Iso.refl _)
  · exact Scheme.forgetToLocallyRingedSpace.congr_map (Scheme.isoSpec_hom_naturality i)
  · exact Scheme.forgetToLocallyRingedSpace.congr_map (Scheme.isoSpec_hom_naturality j)
  · change (inl i j).toLRSHom = (inl i j).toLRSHom ≫ 𝟙 _
    rw [Category.comp_id]
  · change (inr i j).toLRSHom = (inr i j).toLRSHom ≫ 𝟙 _
    rw [Category.comp_id]

/-- Integrality of the second leg transfers to its global-section ring map. -/
lemma appTop_isIntegral [IsIntegralHom j] : j.appTop.hom.IsIntegral := by
  apply IsIntegralHom.SpecMap_iff.mp
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsIntegralHom Z.isoSpec.hom,
    Scheme.isoSpec_hom_naturality]
  infer_instance

/-- The affine left cocone map is integral. -/
lemma inl_isIntegral [IsClosedImmersion i] [IsIntegralHom j] :
    IsIntegralHom (inl i j) := by
  have := isIntegralHom_specMap_pullbackFst i.appTop j.appTop
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2 (appTop_isIntegral j)
  exact inferInstanceAs (IsIntegralHom (X.isoSpec.hom ≫ _))

omit [IsAffine Z] in
/-- The affine right cocone map is a closed immersion. -/
lemma inr_isClosedImmersion [IsClosedImmersion i] : IsClosedImmersion (inr i j) := by
  have := isClosedImmersion_specMap_pullbackSnd i.appTop j.appTop
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
  exact inferInstanceAs (IsClosedImmersion (Y.isoSpec.hom ≫ _))

end Langlands.AlgebraicGeometry.IntegralSchemePushout.AffineSpan
