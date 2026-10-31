import Langlands.Cohomology.DerivedPlusSourceFunctoriality
import Langlands.Geometry.EtaleDerivedPlusPullback
import Langlands.Geometry.EtaleDerivedPullbackFunctoriality

/-! # Identity and composition of bounded-below derived etale pullback -/

noncomputable section

namespace Langlands.Geometry.EtalePullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology

universe u wX wY wZ wT

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
variable (R : Type u) [CommRing R]
variable [HasDerivedCategory.{wX} (EtaleDerivedSections.ModuleSheaf X R)]
  [HasDerivedCategory.{wY} (EtaleDerivedSections.ModuleSheaf Y R)]
  [HasDerivedCategory.{wT} (ModuleCat.{u} R)]

/-- The section chain map followed by a target resolution map, extended by
zero to a morphism of bounded-below complexes. -/
def derivedResolutionSectionsMapWithCoefficients
    {F : EtaleDerivedSections.ModuleSheaf X R} {G : EtaleDerivedSections.ModuleSheaf Y R}
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : (restrictedResolution f R I).cocomplex ⟶ J.cocomplex) :
    DerivedPlusSource.imageResolution (EtaleDerivedSections.sections X R) I ⟶
      DerivedPlusSource.imageResolution (EtaleDerivedSections.sections Y R) J :=
  ObjectProperty.homMk (HomologicalComplex.extendMap
    (resolutionSectionsMap f R I ≫
      ((EtaleDerivedSections.sections Y R).mapHomologicalComplex _).map φ)
    ComplexShape.embeddingUpNat)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A map of target coefficients can be computed on arbitrary compatible
injective resolutions, before localization. -/
theorem derivedSectionsMapWithCoefficients_ofResolutions
    {F : EtaleDerivedSections.ModuleSheaf X R} {G : EtaleDerivedSections.ModuleSheaf Y R}
    (α : (restriction f (ModuleCat.{u} R)).obj F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : (restrictedResolution f R I).cocomplex ⟶ J.cocomplex)
    (comm : (restrictedResolution f R I).ι.f 0 ≫ φ.f 0 = α ≫ J.ι.f 0) :
    derivedSectionsMapWithCoefficients f R α =
      (DerivedPlusSource.imageResolutionIso (EtaleDerivedSections.sections X R) I).hom ≫
        DerivedCategory.Plus.Q.map (derivedResolutionSectionsMapWithCoefficients f R I J φ) ≫
          (DerivedPlusSource.imageResolutionIso (EtaleDerivedSections.sections Y R) J).inv := by
  let φ' : InjectiveResolution.Hom (restrictedResolution f R I) J α :=
    { hom := φ
      ι_f_zero_comp_hom_f_zero := comm.trans
        (by rw [CochainComplex.single₀_map_f_zero]) }
  have h := DerivedPlusSource.derivedMap_comp_map_ofResolutions
    (EtaleDerivedSections.sections X R) (restriction f (ModuleCat.{u} R))
    (EtaleDerivedSections.sections Y R) (sectionsMap f R) α I J φ'
  change derivedSectionsMapWithCoefficients f R α = _ at h
  rw [h]
  congr 2
  apply congrArg DerivedCategory.Plus.Q.map
  apply (CochainComplex.Plus.ι (ModuleCat.{u} R)).map_injective
  exact (HomologicalComplex.extendMap_comp _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 800000 in
/-- Derived pullback along the identity is the identity after the canonical
identification of identity restriction. -/
theorem derivedSectionsMap_id (F : EtaleDerivedSections.ModuleSheaf X R) :
    (derivedSectionsMap (𝟙 X) R).app F ≫
        (EtaleDerivedSectionsPlus.derivedSections X R).map
          ((restrictionId (ModuleCat.{u} R)).hom.app F) =
      𝟙 ((EtaleDerivedSectionsPlus.derivedSections X R).obj F) := by
  change derivedSectionsMapWithCoefficients (𝟙 X) R _ = _
  rw [derivedSectionsMapWithCoefficients_ofResolutions (𝟙 X) R _
    (injectiveResolution F) (injectiveResolution F)
    (restrictionIdResolutionMap R (injectiveResolution F))
    (restrictionIdResolutionMap_comm R (injectiveResolution F))]
  dsimp only [derivedResolutionSectionsMapWithCoefficients]
  rw [resolutionSectionsMap_id]
  simp only [HomologicalComplex.extendMap_id]
  change _ ≫ DerivedCategory.Plus.Q.map (𝟙 _) ≫ _ = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id]
  rfl

variable {Z : Scheme.{u}}
variable [HasDerivedCategory.{wZ} (EtaleDerivedSections.ModuleSheaf Z R)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Derived pullback respects composition of etale scheme morphisms after the
canonical comparison of successive and composite restrictions. -/
theorem derivedSectionsMap_comp (g : Z ⟶ Y) [Etale g]
    (F : EtaleDerivedSections.ModuleSheaf X R) :
    (derivedSectionsMap f R).app F ≫
        (derivedSectionsMap g R).app ((restriction f (ModuleCat.{u} R)).obj F) ≫
        (EtaleDerivedSectionsPlus.derivedSections Z R).map
          ((restrictionComp f (ModuleCat.{u} R) g).hom.app F) =
      (derivedSectionsMap (g ≫ f) R).app F := by
  change (derivedSectionsMap f R).app F ≫
    derivedSectionsMapWithCoefficients g R _ = _
  rw [derivedSectionsMapWithCoefficients_ofResolutions g R _
    (restrictedResolution f R (injectiveResolution F))
    (restrictedResolution (g ≫ f) R (injectiveResolution F))
    (restrictionCompResolutionMap f R g (injectiveResolution F))
    (restrictionCompResolutionMap_comm f R g (injectiveResolution F)),
    derivedSectionsMap_app f R (injectiveResolution F),
    derivedSectionsMap_app (g ≫ f) R (injectiveResolution F)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp_assoc]
  congr 2
  apply congrArg DerivedCategory.Plus.Q.map
  apply (CochainComplex.Plus.ι (ModuleCat.{u} R)).map_injective
  change HomologicalComplex.extendMap _ _ ≫ HomologicalComplex.extendMap _ _ =
    HomologicalComplex.extendMap _ _
  rw [← HomologicalComplex.extendMap_comp]
  exact congrArg (fun k => HomologicalComplex.extendMap k ComplexShape.embeddingUpNat)
    (resolutionSectionsMap_comp f R g (injectiveResolution F))

end Langlands.Geometry.EtalePullback
