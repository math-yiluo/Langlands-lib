import Langlands.Geometry.EtaleDerivedGlobalNormalization
import Langlands.Geometry.EtaleInverseImageCoherence

/-! # Identity and composition for actual geometric section pullback -/

noncomputable section

universe u

namespace Langlands.Geometry.EtaleDerivedGlobalPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open EtaleInverseImage EtaleDerivedSections
open Langlands.Shimura.Coefficients

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z V : Scheme.{u}} (R : Type u) [CommRing R]

/-- Evaluation at the terminal object respects the actual identity direct image. -/
theorem terminalSectionsIso_id (F : ModuleSheaf X R) :
    (EtaleDerivedDirectImage.terminalSectionsIso (𝟙 X) R).hom.app F =
      ((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
        (op (⊤_ X.Etale))).map
          ((EtaleDirectImage.directImageId (ModuleCat.{u} R) X).hom.app F) := by
  change F.obj.map _ = F.obj.map _
  congr 1
  apply Quiver.Hom.unop_inj
  exact (isLimitOfHasTerminalOfPreservesLimit (etaleObjectPullback (𝟙 X))).hom_ext _ _

/-- Global-section comparison respects actual identity direct image. -/
@[reassoc] theorem directImageSectionsIso_id (F : ModuleSheaf X R) :
    (EtaleDerivedDirectImage.directImageSectionsIso (𝟙 X) R).hom.app F =
      (sections X R).map
        ((EtaleDirectImage.directImageId (ModuleCat.{u} R) X).hom.app F) := by
  apply (cancel_mono ((sectionsIso X R).hom.app F)).mp
  simp only [EtaleDerivedDirectImage.directImageSectionsIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, NatTrans.comp_app,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [terminalSectionsIso_id]
  exact ((sectionsIso X R).hom.naturality _).symm

/-- Terminal evaluation respects actual composite geometric direct image. -/
@[reassoc] theorem terminalSectionsIso_comp (f : Z ⟶ X) (g : V ⟶ Z)
    (F : ModuleSheaf V R) :
    (EtaleDerivedDirectImage.terminalSectionsIso f R).hom.app
          ((EtaleDirectImage.directImage g (ModuleCat.{u} R)).obj F) ≫
        (EtaleDerivedDirectImage.terminalSectionsIso g R).hom.app F =
      ((sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj
          (op (⊤_ X.Etale))).map
          ((EtaleDirectImage.directImageComp (ModuleCat.{u} R) f g).hom.app F) ≫
        (EtaleDerivedDirectImage.terminalSectionsIso (g ≫ f) R).hom.app F := by
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
  rw [← F.obj.map_comp, ← F.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  exact (isLimitOfHasTerminalOfPreservesLimit
    (etaleObjectPullback f ⋙ etaleObjectPullback g)).hom_ext _ _

/-- Global-section comparison respects actual composite geometric direct image. -/
@[reassoc] theorem directImageSectionsIso_comp (f : Z ⟶ X) (g : V ⟶ Z)
    (F : ModuleSheaf V R) :
    (EtaleDerivedDirectImage.directImageSectionsIso f R).hom.app
          ((EtaleDirectImage.directImage g (ModuleCat.{u} R)).obj F) ≫
        (EtaleDerivedDirectImage.directImageSectionsIso g R).hom.app F =
      (sections X R).map
          ((EtaleDirectImage.directImageComp (ModuleCat.{u} R) f g).hom.app F) ≫
        (EtaleDerivedDirectImage.directImageSectionsIso (g ≫ f) R).hom.app F := by
  apply (cancel_mono ((sectionsIso V R).hom.app F)).mp
  simp only [EtaleDerivedDirectImage.directImageSectionsIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, NatTrans.comp_app,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc,
    Category.comp_id]
  rw [terminalSectionsIso_comp]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  exact ((sectionsIso X R).hom.naturality _).symm

/-- The ordinary geometric identity unit is the inverse-image identity map,
through the actual direct-image comparison. -/
@[reassoc] theorem inverseImageIdentity_unit (F : ModuleSheaf X R) :
    (inverseImageAdjunction (𝟙 X) R).unit.app F ≫
        (EtaleDirectImage.directImageId (ModuleCat.{u} R) X).hom.app
          ((inverseImage (𝟙 X) R).obj F) =
      (inverseImageId R X).inv.app F := by
  apply (cancel_mono ((inverseImageId R X).hom.app F)).mp
  have h := unit_conjugateEquiv Adjunction.id
    (inverseImageAdjunction (𝟙 X) R) (inverseImageId R X).hom F
  rw [conjugate_inverseImageId] at h
  simp only [Adjunction.id_unit, NatTrans.id_app, Category.id_comp] at h
  have ht := (EtaleDirectImage.directImageId (ModuleCat.{u} R) X).hom.naturality
    ((inverseImageId R X).hom.app F)
  simp only [Functor.id_map] at ht
  rw [Category.assoc, ← ht, ← Category.assoc, ← h]
  simp

/-- Ordinary global-section pullback along the identity has its canonical
coefficient identification. -/
@[reassoc] theorem sectionsPullback_id (F : ModuleSheaf X R) :
    (sectionsPullback (𝟙 X) R).app F ≫
        (sections X R).map ((inverseImageId R X).hom.app F) = 𝟙 _ := by
  simp only [sectionsPullback, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Category.id_comp]
  rw [directImageSectionsIso_id, ← Functor.map_comp,
    inverseImageIdentity_unit, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id]
  rfl

/-- The actual composite geometric adjunction unit intertwines inverse-image
composition and direct-image composition. -/
@[reassoc] theorem inverseImageComposition_unit (f : Z ⟶ X) (g : V ⟶ Z)
    (F : ModuleSheaf X R) :
    (inverseImageAdjunction f R).unit.app F ≫
        (EtaleDirectImage.directImage f (ModuleCat.{u} R)).map
          ((inverseImageAdjunction g R).unit.app ((inverseImage f R).obj F)) ≫
        (EtaleDirectImage.directImage f (ModuleCat.{u} R)).map
          ((EtaleDirectImage.directImage g (ModuleCat.{u} R)).map
            ((inverseImageComp R f g).hom.app F)) ≫
        (EtaleDirectImage.directImageComp (ModuleCat.{u} R) f g).hom.app
          ((inverseImage (g ≫ f) R).obj F) =
      (inverseImageAdjunction (g ≫ f) R).unit.app F := by
  have h := unit_conjugateEquiv (inverseImageAdjunction (g ≫ f) R)
    ((inverseImageAdjunction f R).comp (inverseImageAdjunction g R))
    (inverseImageComp R f g).hom F
  rw [conjugate_inverseImageComp] at h
  simp only [Adjunction.comp_unit_app, Functor.comp_map] at h
  rw [← Category.assoc, ← Category.assoc, ← h, Category.assoc,
    Iso.inv_hom_id_app]
  erw [Category.comp_id]

/-- Ordinary geometric section pullback respects composition, with the actual
coefficient comparison from uniqueness of left adjoints. -/
@[reassoc] theorem sectionsPullback_comp (f : Z ⟶ X) (g : V ⟶ Z)
    (F : ModuleSheaf X R) :
    (sectionsPullback f R).app F ≫
        (sectionsPullback g R).app ((inverseImage f R).obj F) ≫
        (sections V R).map ((inverseImageComp R f g).hom.app F) =
      (sectionsPullback (g ≫ f) R).app F := by
  have hg := (EtaleDerivedDirectImage.directImageSectionsIso g R).hom.naturality
    ((inverseImageComp R f g).hom.app F)
  have hf := (EtaleDerivedDirectImage.directImageSectionsIso f R).hom.naturality
    ((inverseImageAdjunction g R).unit.app ((inverseImage f R).obj F))
  have hf' := (EtaleDerivedDirectImage.directImageSectionsIso f R).hom.naturality
    ((EtaleDirectImage.directImage g (ModuleCat.{u} R)).map
      ((inverseImageComp R f g).hom.app F))
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hg hf hf'
  simp only [sectionsPullback, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Category.id_comp, Category.assoc]
  rw [← hg, ← reassoc_of% hf, ← reassoc_of% hf',
    directImageSectionsIso_comp, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [inverseImageComposition_unit]

/-- Successive actual section pullbacks before identifying coefficient inverse
images with inverse image along the composite. -/
def compositeSectionsPullback (f : Z ⟶ X) (g : V ⟶ Z) :
    sections X R ⟶ (inverseImage f R ⋙ inverseImage g R) ⋙ sections V R :=
  sectionsPullback f R ≫
    Functor.whiskerLeft (inverseImage f R) (sectionsPullback g R) ≫
    (Functor.associator _ _ _).inv

/-- The successive section map is the constructed map for the composite. -/
theorem compositeSectionsPullback_eq (f : Z ⟶ X) (g : V ⟶ Z) :
    compositeSectionsPullback R f g ≫
        Functor.whiskerRight (inverseImageComp R f g).hom (sections V R) =
      sectionsPullback (g ≫ f) R := by
  apply NatTrans.ext
  funext F
  simpa [compositeSectionsPullback] using sectionsPullback_comp R f g F

end Langlands.Geometry.EtaleDerivedGlobalPullback
