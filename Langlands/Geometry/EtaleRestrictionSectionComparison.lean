import Langlands.Geometry.EtaleDerivedGlobalNormalization
import Langlands.Geometry.EtaleInverseImageRestriction

/-! # Agreement of actual geometric section pullback with etale restriction -/

noncomputable section

universe u

namespace Langlands.Geometry.EtaleDerivedGlobalPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open EtaleInverseImage EtaleDerivedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z : Scheme.{u}} (f : Z ⟶ X) [Etale f]
  (R : Type u) [CommRing R]

/-- Along an etale map, the constructed inverse image preserves injectives
through its actual comparison with etale restriction. -/
instance inverseImage_etale_preservesInjectives :
    (inverseImage f R).PreservesInjectiveObjects where
  injective_obj {F} hF :=
    Injective.of_iso ((inverseImageIsoRestriction f R).app F).symm
      ((EtalePullback.restriction f (ModuleCat.{u} R)).injective_obj_of_injective hF)

/-- The actual etale geometric inverse image on the full injective
subcategories, with its injective property proved through restriction. -/
def inverseImageInjectives : InjectiveObject (ModuleSheaf X R) ⥤
    InjectiveObject (ModuleSheaf Z R) :=
  ObjectProperty.lift _
    (InjectiveObject.ι (ModuleSheaf X R) ⋙ inverseImage f R) (fun J =>
      (inverseImage f R).injective_obj_of_injective J.property)

instance inverseImageInjectives_additive : (inverseImageInjectives f R).Additive := by
  dsimp only [inverseImageInjectives]
  infer_instance

/-- The constructed inverse-image/restriction comparison respects the two
actual geometric adjunction units. -/
@[reassoc] theorem inverseImageIsoRestriction_unit (F : ModuleSheaf X R) :
    (inverseImageAdjunction f R).unit.app F ≫
      (EtaleDirectImage.directImage f (ModuleCat.{u} R)).map
        ((inverseImageIsoRestriction f R).hom.app F) =
    (restrictionGeometricAdjunction f (ModuleCat.{u} R)).unit.app F :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ F

/-- The site composition/base-change unit induces the original terminal-section
restriction map through the preserved-terminal comparison. -/
@[reassoc] theorem restrictionGeometricUnit_terminalSections (F : ModuleSheaf X R) :
    ((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (op (⊤_ X.Etale))).map
        ((restrictionGeometricAdjunction f (ModuleCat.{u} R)).unit.app F) ≫
      (EtaleDerivedDirectImage.terminalSectionsIso f R).hom.app
        ((EtalePullback.restriction f (ModuleCat.{u} R)).obj F) =
    (EtalePullback.terminalSectionsMap f (ModuleCat.{u} R)).app F := by
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _
  rw [← F.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  exact terminalIsTerminal.hom_ext _ _

/-- The same unit formula for the existing global-section functors. -/
@[reassoc] theorem restrictionGeometricUnit_sections (F : ModuleSheaf X R) :
    (sections X R).map
        ((restrictionGeometricAdjunction f (ModuleCat.{u} R)).unit.app F) ≫
      (EtaleDerivedDirectImage.directImageSectionsIso f R).hom.app
        ((EtalePullback.restriction f (ModuleCat.{u} R)).obj F) =
    (EtalePullback.sectionsMap f R).app F := by
  have hn := (sectionsIso X R).hom.naturality
    ((restrictionGeometricAdjunction f (ModuleCat.{u} R)).unit.app F)
  simp only [EtaleDerivedDirectImage.directImageSectionsIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, NatTrans.comp_app,
    Iso.symm_hom, EtalePullback.sectionsMap]
  rw [reassoc_of% hn, restrictionGeometricUnit_terminalSections_assoc]

/-- Ordinary arbitrary-morphism section pullback agrees with the earlier
etale-restriction map through the actual coefficient isomorphism. -/
@[reassoc] theorem sectionsPullback_restriction (F : ModuleSheaf X R) :
    (sectionsPullback f R).app F ≫
      (sections Z R).map ((inverseImageIsoRestriction f R).hom.app F) =
    (EtalePullback.sectionsMap f R).app F := by
  have hn := (EtaleDerivedDirectImage.directImageSectionsIso f R).hom.naturality
    ((inverseImageIsoRestriction f R).hom.app F)
  dsimp only [Functor.comp_map] at hn
  simp only [sectionsPullback, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Category.id_comp, Category.assoc]
  rw [← hn, ← Functor.map_comp_assoc, inverseImageIsoRestriction_unit,
    restrictionGeometricUnit_sections]

/-- Equality of the natural ordinary section transformations after the
constructed inverse-image/restriction identification. -/
theorem sectionsPullback_restriction_eq :
    sectionsPullback f R ≫
      Functor.whiskerRight (inverseImageIsoRestriction f R).hom (sections Z R) =
    EtalePullback.sectionsMap f R := by
  apply NatTrans.ext
  funext F
  exact sectionsPullback_restriction f R F

end Langlands.Geometry.EtaleDerivedGlobalPullback
