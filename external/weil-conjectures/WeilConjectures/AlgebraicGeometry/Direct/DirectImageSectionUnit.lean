/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedAdjunctionTopEdgeData
public import WeilConjectures.Topology.OpenModuleCohomology

/-! # The cochain unit for local sections of a direct image

Source: Stacks Project, Cohomology, Tags 079V, 0D5W and 0D5X.
(blueprint: def-weil-pbc-direct-image-section-unit).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
namespace RingedSpace

/-- The standard derived unit has the universal factorization bijection.
Source: Stacks, Tag 079V (blueprint: def-weil-pbc-direct-image-section-unit). -/
theorem standardRightDerived_universal
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (G : DerivedCategory C ⥤ DerivedCategory D) :
    Function.Bijective (fun b : F.rightDerivedFunctor ⟶ G ↦
      F.rightDerivedFunctorUnit ≫ Functor.whiskerLeft DerivedCategory.Qh b) := by
  constructor
  · intro a b hab
    exact F.rightDerivedFunctor.rightDerived_ext F.rightDerivedFunctorUnit
      (HomotopyCategory.quasiIso C (.up ℤ)) G a b hab
  · intro a
    exact ⟨F.rightDerivedFunctor.rightDerivedDesc F.rightDerivedFunctorUnit
      (HomotopyCategory.quasiIso C (.up ℤ)) G a,
        F.rightDerivedFunctor.rightDerived_fac F.rightDerivedFunctorUnit
          (HomotopyCategory.quasiIso C (.up ℤ)) G a⟩

/-- The unique natural comparison preserving the two derived units.
Source: Stacks, Tag 079V (blueprint: def-weil-pbc-direct-image-section-unit). -/
def sectionStandardDirectImageIso {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))] (f : X ⟶ Y) :
    RingedSpace.sectionDerivedDirectImage f ≅ RingedSpace.derivedModuleDirectImage f :=
  Classical.choose
    ((RingedSpace.moduleDirectImage f).rightDerivedFunctorOfQuasiIsoResolutions_unique
      (RingedSpace.localSectionsEnoughKInjectives X) _
      (RingedSpace.moduleDirectImage f).rightDerivedFunctorUnit
      (standardRightDerived_universal (RingedSpace.moduleDirectImage f)))

/-- The comparison preserves the homotopy-category derived units.
Source: Stacks, Tag 079V (blueprint: def-weil-pbc-direct-image-section-unit). -/
theorem sectionStandardDirectImageIso_fac {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))] (f : X ⟶ Y) :
    (RingedSpace.moduleDirectImage f).rightDerivedFunctorOfQuasiIsoResolutionsUnit
        (RingedSpace.localSectionsEnoughKInjectives X) ≫
      Functor.whiskerLeft DerivedCategory.Qh (sectionStandardDirectImageIso f).hom =
        (RingedSpace.moduleDirectImage f).rightDerivedFunctorUnit :=
  (Classical.choose_spec
    ((RingedSpace.moduleDirectImage f).rightDerivedFunctorOfQuasiIsoResolutions_unique
      (RingedSpace.localSectionsEnoughKInjectives X) _
      (RingedSpace.moduleDirectImage f).rightDerivedFunctorUnit
      (standardRightDerived_universal (RingedSpace.moduleDirectImage f)))).1

private theorem sectionStandardDirectImageIso_model {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))] (f : X ⟶ Y)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ) [I.IsKInjective] :
    ((RingedSpace.moduleDirectImage f).rightDerivedFunctorOfQuasiIsoResolutionsObjIso
      (RingedSpace.localSectionsEnoughKInjectives X) (𝟙 I)).inv ≫
        (sectionStandardDirectImageIso f).hom.app (DerivedCategory.Q.obj I) =
      ((RingedSpace.moduleDirectImage f).rightDerivedFunctorObjQIso I).inv := by
  have hf := congrArg (fun a ↦ a.app ((HomotopyCategory.quotient _ (.up ℤ)).obj I))
    (sectionStandardDirectImageIso_fac f)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
  unfold Functor.rightDerivedFunctorOfQuasiIsoResolutionsObjIso
    Functor.rightDerivedFunctorObjQIso
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, asIso_hom,
    Iso.app_inv, Iso.app_hom, asIso_inv, IsIso.inv_id,
    CategoryTheory.Functor.map_id,
    Category.comp_id, Category.assoc]
  rw [((sectionStandardDirectImageIso f).hom.naturality
    ((DerivedCategory.quotientCompQhIso _).hom.app I))]
  simpa only [Category.assoc, RingedSpace.derivedModuleDirectImage, Functor.comp_obj]
    using congrArg (fun a ↦
    (DerivedCategory.quotientCompQhIso _).inv.app
      (((RingedSpace.moduleDirectImage f).mapHomologicalComplex (.up ℤ)).obj I) ≫ a ≫
        (RingedSpace.moduleDirectImage f).rightDerivedFunctor.map
          ((DerivedCategory.quotientCompQhIso _).hom.app I)) hf

/-- The pointwise model comparison is the natural comparison component.
Source: Stacks, Tag 079V (blueprint: def-weil-pbc-direct-image-section-unit). -/
theorem topEdgeDirectImageComparison_eq {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))] (f : X ⟶ Y)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings X))) :
    (RingedSpace.topEdgeDirectImageComparison f K).hom =
      (sectionStandardDirectImageIso f).hom.app K := by
  let I := RingedSpace.topEdgeResolution X K
  let r := RingedSpace.topEdgeResolutionIso X K
  have hm := sectionStandardDirectImageIso_model f I
  have hm' :
      ((RingedSpace.moduleDirectImage f).rightDerivedFunctorOfQuasiIsoResolutionsObjIso
        (RingedSpace.localSectionsEnoughKInjectives X) (𝟙 I)).hom ≫
          ((RingedSpace.moduleDirectImage f).rightDerivedFunctorObjQIso I).inv =
        (sectionStandardDirectImageIso f).hom.app (DerivedCategory.Q.obj I) := by
    rw [← hm]
    simp
  unfold RingedSpace.topEdgeDirectImageComparison
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv]
  rw [reassoc_of% hm']
  rw [reassoc_of% ((sectionStandardDirectImageIso f).hom.naturality
    (RingedSpace.topEdgeResolutionIso X K).inv)]
  simp only [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]

/-- The canonical natural comparison from inverse-open cohomology to local cohomology
of the standard derived direct image. It is Leray followed by the unique unit-preserving
comparison of the two derived direct images.
Source: Stacks, Tags 0D5W and 0D5X
(blueprint: def-weil-pbc-direct-image-section-unit). -/
def directImageSectionComparison {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))] (f : X ⟶ Y) (q : ℤ) :
    inverseOpenHypercohomologyPresheaf f q ⟶
      derivedModuleDirectImage f ⋙ localHypercohomologyPresheaf Y q :=
  localHypercohomologyComparison f q ≫
    Functor.whiskerRight (sectionStandardDirectImageIso f).hom
      (localHypercohomologyPresheaf Y q)

/-- This natural comparison is the inverse of the published pointwise Leray comparison.
Source: Stacks, Tags 0D5W and 0D5X
(blueprint: def-weil-pbc-direct-image-section-unit). -/
theorem directImageSectionComparison_eq {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))] (f : X ⟶ Y) (q : ℤ)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings X))) :
    (directImageSectionComparison f q).app K = (topEdgeLocalLeray f q K).inv := by
  unfold directImageSectionComparison topEdgeLocalLeray
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Iso.trans_inv,
    Iso.symm_inv, Functor.mapIso_inv, Iso.app_inv]
  rw [topEdgeDirectImageComparison_eq]
  exact congrArg (fun a ↦ a.app K ≫
    (localHypercohomologyPresheaf Y q).map ((sectionStandardDirectImageIso f).hom.app K))
      (Classical.choose_spec (unboundedDirectImage_sectionPresheaf f q)).1.symm

/-- The inverse-open derived unit on cochains. Its source is the actual presheaf of
sections of the termwise direct image.
Source: Stacks, Tags 079V and 0D5X
(blueprint: def-weil-pbc-direct-image-section-unit). -/
def inverseOpenUnitQ {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))] (f : X ⟶ Y) :
    (moduleDirectImage f ⋙ localAbelianSections Y).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙
        (moduleDirectImage f ⋙ localAbelianSections Y).rightDerivedFunctorOfQuasiIsoResolutions
          (localSectionsEnoughKInjectives X) :=
  let P := moduleDirectImage f ⋙ localAbelianSections Y
  (Functor.isoWhiskerLeft (P.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso _)).inv ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ (.up ℤ))
      (P.rightDerivedFunctorOfQuasiIsoResolutionsUnit
        (localSectionsEnoughKInjectives X)) ≫
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _)
      (P.rightDerivedFunctorOfQuasiIsoResolutions
        (localSectionsEnoughKInjectives X))).hom

/-- On a K-injective input the inverse-open unit is the inverse model comparison.
Source: Stacks, Tag 079V (blueprint: def-weil-pbc-direct-image-section-unit). -/
theorem inverseOpenUnitQ_model {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))] (f : X ⟶ Y)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ) [I.IsKInjective] :
    (inverseOpenUnitQ f).app I =
      ((moduleDirectImage f ⋙ localAbelianSections Y).rightDerivedFunctorOfQuasiIsoResolutionsObjIso
          (localSectionsEnoughKInjectives X) (𝟙 I)).inv := by
  simp only [inverseOpenUnitQ, Functor.rightDerivedFunctorOfQuasiIsoResolutionsObjIso,
    NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.trans_inv,
    Functor.mapIso_inv, Iso.symm_inv, Iso.app_inv, asIso_inv, asIso_hom,
    CategoryTheory.Functor.map_id, IsIso.inv_id, Category.comp_id, Category.assoc]
  rfl

end RingedSpace

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The inverse-open cochain unit, followed by the canonical Leray comparison, gives
sections of the standard derived direct image. This is natural for every cochain map.
Source: Stacks, Tags 079V, 0D5W and 0D5X
(blueprint: def-weil-pbc-direct-image-section-unit). -/
def directImageSectionUnit {X S : Scheme.{u}} (f : X ⟶ S) (q : ℤ) :
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
        RingedSpace.localAbelianSections S.toRingedSpace).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.homologyFunctor _ (.up ℤ) q ⟶
      DerivedCategory.Q ⋙ schemeDerivedDirectImage f ⋙
        RingedSpace.localHypercohomologyPresheaf S.toRingedSpace q :=
  let P := RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
    RingedSpace.localAbelianSections S.toRingedSpace
  Functor.whiskerLeft (P.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.homologyFunctorFactors _ q).inv ≫
    Functor.whiskerRight (RingedSpace.inverseOpenUnitQ f.toLRSHom.toShHom)
      (DerivedCategory.homologyFunctor _ q) ≫
    Functor.whiskerLeft DerivedCategory.Q
      (RingedSpace.directImageSectionComparison f.toLRSHom.toShHom q)

/-- Evaluate the unit using the exact evaluation/homology comparison on the source.
Source: Stacks Project, Tag 0D5X (blueprint: def-weil-pbc-direct-image-section-unit). -/
def directImageSectionUnitAt {X S : Scheme.{u}} (f : X ⟶ S) (q : ℤ) (V : S.Opens)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    (((RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)).mapHomologicalComplex
      (.up ℤ)).obj K).homology q ⟶
    ((RingedSpace.localHypercohomologyPresheaf S.toRingedSpace q).obj
      ((schemeDerivedDirectImage f).obj (DerivedCategory.Q.obj K))).obj (op V) :=
  let P := RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
    RingedSpace.localAbelianSections S.toRingedSpace
  let E := (CategoryTheory.evaluation S.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)
  ((((P.mapHomologicalComplex (.up ℤ)).obj K).sc q).mapHomologyIso E).hom ≫
    ((directImageSectionUnit f q).app K).app (op V)

/-- Naturality of the evaluated cochain unit. Both the evaluation/homology comparison
and the derived units are natural transformations.
Source: Stacks Project, Tags 079V and 0D5X
(blueprint: def-weil-pbc-direct-image-section-unit). -/
theorem directImageSectionUnitAt_naturality {X S : Scheme.{u}} (f : X ⟶ S)
    (q : ℤ) (V : S.Opens)
    {K L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ}
    (a : K ⟶ L) :
    HomologicalComplex.homologyMap
        (((RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)).mapHomologicalComplex
           (.up ℤ)).map a) q ≫ directImageSectionUnitAt f q V L =
      directImageSectionUnitAt f q V K ≫
        ((RingedSpace.localHypercohomologyPresheaf S.toRingedSpace q).map
          ((schemeDerivedDirectImage f).map (DerivedCategory.Q.map a))).app (op V) := by
  let P := RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
    RingedSpace.localAbelianSections S.toRingedSpace
  let E := (CategoryTheory.evaluation S.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)
  have h₁ := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ q).map
      ((P.mapHomologicalComplex (.up ℤ)).map a)) E
  have h₂ := congrArg (fun t ↦ t.app (op V)) ((directImageSectionUnit f q).naturality a)
  have h₂' : E.map (HomologicalComplex.homologyMap
      ((P.mapHomologicalComplex (.up ℤ)).map a) q) ≫
        ((directImageSectionUnit f q).app L).app (op V) =
      ((directImageSectionUnit f q).app K).app (op V) ≫
        ((RingedSpace.localHypercohomologyPresheaf S.toRingedSpace q).map
          ((schemeDerivedDirectImage f).map (DerivedCategory.Q.map a))).app (op V) := h₂
  exact (congrArg (fun t ↦ t ≫ ((directImageSectionUnit f q).app L).app (op V)) h₁).trans
    ((Category.assoc _ _ _).trans ((congrArg (fun t ↦
      ((((P.mapHomologicalComplex (.up ℤ)).obj K).sc q).mapHomologyIso E).hom ≫ t) h₂').trans
        (Category.assoc _ _ _).symm))

end AlgebraicGeometry
