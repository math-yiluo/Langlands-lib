import Langlands.Geometry.EtaleDerivedPullback

/-!
# Functoriality of pullback on ordinary étale cohomology

Resolution formulas and identity/composition compatibility for the constructed maps.
-/

noncomputable section

namespace Langlands.Geometry.EtalePullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
variable (R : Type u) [CommRing R]

/-- The natural comparison can be computed with any injective resolution. -/
theorem restrictionDerivedIso_app_ofResolution
    {F : EtaleDerivedSections.ModuleSheaf X R} (I : InjectiveResolution F) (q : ℕ) :
    (restrictionDerivedIso f R q).hom.app F =
      (restrictionDerivedIsoOfResolution f R I q).hom := by
  have h := restrictionDerivedIsoOfResolution_naturality f R (𝟙 F)
    (injectiveResolution F) I
    (InjectiveResolution.desc (𝟙 F) I (injectiveResolution F))
    (InjectiveResolution.desc_commutes_zero (𝟙 F) I (injectiveResolution F)) q
  simpa [restrictionDerivedIso] using h.symm

/-- The cohomology map is computed on any chosen injective resolution. -/
theorem cohomologyMap_app_ofResolution
    {F : EtaleDerivedSections.ModuleSheaf X R} (I : InjectiveResolution F) (q : ℕ) :
    (cohomologyMap f R q).app F =
      (I.isoRightDerivedObj (EtaleDerivedSections.sections X R) q).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q).map
          (resolutionSectionsMap f R I) ≫
        ((restrictedResolution f R I).isoRightDerivedObj
          (EtaleDerivedSections.sections Y R) q).inv := by
  dsimp only [cohomologyMap, NatTrans.comp_app]
  rw [restrictionDerivedIso_app_ofResolution f R I,
    InjectiveResolution.rightDerived_app_eq (sectionsMap f R) I]
  dsimp only [restrictionDerivedIsoOfResolution, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- A coefficient morphism can be computed by any compatible lift to resolutions. -/
theorem cohomologyMapWithCoefficients_ofResolutions (q : ℕ)
    {F : EtaleDerivedSections.ModuleSheaf X R} {G : EtaleDerivedSections.ModuleSheaf Y R}
    (α : (restriction f (ModuleCat.{u} R)).obj F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : (restrictedResolution f R I).cocomplex ⟶ J.cocomplex)
    (comm : (restrictedResolution f R I).ι.f 0 ≫ φ.f 0 = α ≫ J.ι.f 0) :
    cohomologyMapWithCoefficients f R q α =
      (I.isoRightDerivedObj (EtaleDerivedSections.sections X R) q).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q).map
          (resolutionSectionsMap f R I ≫
            ((EtaleDerivedSections.sections Y R).mapHomologicalComplex _).map φ) ≫
        (J.isoRightDerivedObj (EtaleDerivedSections.sections Y R) q).inv := by
  have h := InjectiveResolution.isoRightDerivedObj_inv_naturality α
    (restrictedResolution f R I) J φ comm (EtaleDerivedSections.sections Y R) q
  dsimp only [cohomologyMapWithCoefficients]
  rw [cohomologyMap_app_ofResolution f R I]
  simp only [Category.assoc]
  erw [h]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

/-- Restriction of sections respects composition of étale scheme morphisms. -/
theorem sectionsMap_comp {Z : Scheme.{u}} (g : Z ⟶ Y) [Etale g]
    (F : EtaleDerivedSections.ModuleSheaf X R) :
    (sectionsMap f R).app F ≫
        (sectionsMap g R).app ((restriction f (ModuleCat.{u} R)).obj F) ≫
        (EtaleDerivedSections.sections Z R).map
          ((restrictionComp f (ModuleCat.{u} R) g).hom.app F) =
      (sectionsMap (g ≫ f) R).app F := by
  dsimp only [sectionsMap, NatTrans.comp_app, Functor.whiskerLeft_app]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← (EtaleDerivedSections.sectionsIso Z R).inv.naturality]
  simpa only [Category.assoc] using congrArg
    (fun k => (EtaleDerivedSections.sectionsIso X R).hom.app F ≫ k ≫
      (EtaleDerivedSections.sectionsIso Z R).inv.app
        ((restriction (g ≫ f) (ModuleCat.{u} R)).obj F))
    (terminalSectionsMap_comp f (ModuleCat.{u} R) g F)

/-- Identity restriction acts as the identity on sections. -/
theorem sectionsMap_id (F : EtaleDerivedSections.ModuleSheaf X R) :
    (sectionsMap (𝟙 X) R).app F ≫
        (EtaleDerivedSections.sections X R).map
          ((restrictionId (ModuleCat.{u} R)).hom.app F) =
      𝟙 ((EtaleDerivedSections.sections X R).obj F) := by
  dsimp only [sectionsMap, NatTrans.comp_app, Functor.whiskerLeft_app]
  simp only [Category.assoc]
  rw [← (EtaleDerivedSections.sectionsIso X R).inv.naturality]
  simpa [Category.assoc] using congrArg
    (fun k => (EtaleDerivedSections.sectionsIso X R).hom.app F ≫ k ≫
      (EtaleDerivedSections.sectionsIso X R).inv.app F)
    (terminalSectionsMap_id (ModuleCat.{u} R) F)

/-- The identity restriction identification, applied to a resolution. -/
def restrictionIdResolutionMap
    {F : EtaleDerivedSections.ModuleSheaf X R} (I : InjectiveResolution F) :
    (restrictedResolution (𝟙 X) R I).cocomplex ⟶ I.cocomplex :=
  (NatTrans.mapHomologicalComplex (restrictionId (ModuleCat.{u} R)).hom _).app I.cocomplex

/-- The identity restriction chain map lifts the identity restriction on sheaves. -/
theorem restrictionIdResolutionMap_comm
    {F : EtaleDerivedSections.ModuleSheaf X R} (I : InjectiveResolution F) :
    (restrictedResolution (𝟙 X) R I).ι.f 0 ≫ (restrictionIdResolutionMap R I).f 0 =
      (restrictionId (ModuleCat.{u} R)).hom.app F ≫ I.ι.f 0 := by
  rw [DerivedComparison.mapInjectiveResolution_ι_f_zero]
  exact (restrictionId (ModuleCat.{u} R)).hom.naturality (I.ι.f 0)

/-- The section chain map for an identity is the identity after identification. -/
theorem resolutionSectionsMap_id
    {F : EtaleDerivedSections.ModuleSheaf X R} (I : InjectiveResolution F) :
    resolutionSectionsMap (𝟙 X) R I ≫
        ((EtaleDerivedSections.sections X R).mapHomologicalComplex _).map
          (restrictionIdResolutionMap R I) = 𝟙 _ := by
  ext n : 1
  exact sectionsMap_id R (I.cocomplex.X n)

set_option maxHeartbeats 800000 in
/-- Pullback along the identity induces the identity in every cohomology degree. -/
theorem cohomologyMap_id (q : ℕ) (F : EtaleDerivedSections.ModuleSheaf X R) :
    (cohomologyMap (𝟙 X) R q).app F ≫
        (EtaleDerivedSections.cohomology X R q).map
          ((restrictionId (ModuleCat.{u} R)).hom.app F) =
      𝟙 ((EtaleDerivedSections.cohomology X R q).obj F) := by
  change cohomologyMapWithCoefficients (𝟙 X) R q _ = _
  rw [cohomologyMapWithCoefficients_ofResolutions (𝟙 X) R q _
    (injectiveResolution F) (injectiveResolution F)
    (restrictionIdResolutionMap R (injectiveResolution F))
    (restrictionIdResolutionMap_comm R (injectiveResolution F)), resolutionSectionsMap_id]
  simp
  rfl

/-- The composition restriction identification, applied to a resolution. -/
def restrictionCompResolutionMap {Z : Scheme.{u}} (g : Z ⟶ Y) [Etale g]
    {F : EtaleDerivedSections.ModuleSheaf X R} (I : InjectiveResolution F) :
    (restrictedResolution g R (restrictedResolution f R I)).cocomplex ⟶
      (restrictedResolution (g ≫ f) R I).cocomplex :=
  (NatTrans.mapHomologicalComplex
    (restrictionComp f (ModuleCat.{u} R) g).hom _).app I.cocomplex

/-- The composition restriction chain map lifts the composition identification. -/
theorem restrictionCompResolutionMap_comm {Z : Scheme.{u}} (g : Z ⟶ Y) [Etale g]
    {F : EtaleDerivedSections.ModuleSheaf X R} (I : InjectiveResolution F) :
    (restrictedResolution g R (restrictedResolution f R I)).ι.f 0 ≫
        (restrictionCompResolutionMap f R g I).f 0 =
      (restrictionComp f (ModuleCat.{u} R) g).hom.app F ≫
        (restrictedResolution (g ≫ f) R I).ι.f 0 := by
  exact (restrictionComp f (ModuleCat.{u} R) g).hom.naturality (I.ι.f 0)

/-- The section chain maps respect composition after restriction identification. -/
theorem resolutionSectionsMap_comp {Z : Scheme.{u}} (g : Z ⟶ Y) [Etale g]
    {F : EtaleDerivedSections.ModuleSheaf X R} (I : InjectiveResolution F) :
    resolutionSectionsMap f R I ≫
        resolutionSectionsMap g R (restrictedResolution f R I) ≫
        ((EtaleDerivedSections.sections Z R).mapHomologicalComplex _).map
          (restrictionCompResolutionMap f R g I) =
      resolutionSectionsMap (g ≫ f) R I := by
  ext n : 1
  exact sectionsMap_comp f R g (I.cocomplex.X n)

/-- Pullback respects composition in every cohomology degree. -/
theorem cohomologyMap_comp {Z : Scheme.{u}} (g : Z ⟶ Y) [Etale g]
    (q : ℕ) (F : EtaleDerivedSections.ModuleSheaf X R) :
    (cohomologyMap f R q).app F ≫
        (cohomologyMap g R q).app ((restriction f (ModuleCat.{u} R)).obj F) ≫
        (EtaleDerivedSections.cohomology Z R q).map
          ((restrictionComp f (ModuleCat.{u} R) g).hom.app F) =
      (cohomologyMap (g ≫ f) R q).app F := by
  change (cohomologyMap f R q).app F ≫
    cohomologyMapWithCoefficients g R q _ = _
  rw [cohomologyMapWithCoefficients_ofResolutions g R q _
    (restrictedResolution f R (injectiveResolution F))
    (restrictedResolution (g ≫ f) R (injectiveResolution F))
    (restrictionCompResolutionMap f R g (injectiveResolution F))
    (restrictionCompResolutionMap_comm f R g (injectiveResolution F)),
    cohomologyMap_app_ofResolution f R (injectiveResolution F),
    cohomologyMap_app_ofResolution (g ≫ f) R (injectiveResolution F)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, resolutionSectionsMap_comp]

end Langlands.Geometry.EtalePullback
