import Langlands.AlgebraicGeometry.Modules.CohomologyPullbackLawsStatement
import Langlands.Cohomology.DerivedPlusNaturality

/-!
# Degree-zero normalization of canonical relative-cohomology pullback
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology.DerivedPlus

universe w w' v v' u u'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [EnoughInjectives C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
variable (F : C ⥤ D) [F.Additive]

def singlePlus (X : C) : CochainComplex.Plus C :=
  ⟨(CochainComplex.singleFunctor C 0).obj X, ⟨0, inferInstance⟩⟩

def singlePlusIso (X : C) :
    (DerivedCategory.Plus.singleFunctor C 0).obj X ≅
      DerivedCategory.Plus.Q.obj (singlePlus X) :=
  DerivedCategory.Plus.ι.preimageIso
    ((DerivedCategory.Plus.singleFunctorιIso C 0).app X ≪≫
      (DerivedCategory.singleFunctorIsoCompQ C 0).app X ≪≫
      ((DerivedCategory.Plus.QCompιIso C).app (singlePlus X)).symm)

def singleImageIso (X : C) :
    F.mapCochainComplexPlus.obj (singlePlus X) ≅ singlePlus (F.obj X) :=
  ObjectProperty.isoMk _
    ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app X)

def augmentationPlus {X : C} (I : InjectiveResolution X) :
    singlePlus X ⟶ resolutionPlus I :=
  ObjectProperty.homMk I.ι'

omit [EnoughInjectives C] in
set_option backward.isDefEq.respectTransparency false in
lemma singlePlusIso_comp_augmentation {X : C} (I : InjectiveResolution X) :
    (singlePlusIso X).hom ≫ DerivedCategory.Plus.Q.map (augmentationPlus I) =
      (singleIsoOfResolution I).hom := by
  apply DerivedCategory.Plus.ι.map_injective
  have h := (DerivedCategory.Plus.QCompιIso C).inv.naturality (augmentationPlus I)
  simp only [Functor.comp_map] at h
  simp only [singlePlusIso, Functor.preimageIso_hom, Functor.map_preimage,
    Functor.map_comp, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    ι_map_singleIsoOfResolution_hom, Category.assoc]
  exact congrArg (fun g =>
      (DerivedCategory.Plus.singleFunctorιIso C 0).hom.app X ≫
      (DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫ g) h.symm

def zeroUnit (X : C) :
    DerivedCategory.Plus.Q.obj (singlePlus (F.obj X)) ⟶
      (derivedComplex F).obj X :=
  DerivedCategory.Plus.Q.map (singleImageIso F X).inv ≫
    F.rightDerivedFunctorPlusUnit.app (singlePlus X) ≫
      F.rightDerivedFunctorPlus.map (singlePlusIso X).inv

set_option backward.isDefEq.respectTransparency false in
lemma zeroUnit_comp_derivedComplexIso {X : C} (I : InjectiveResolution X) :
    zeroUnit F X ≫ (derivedComplexIso F I).hom =
      DerivedCategory.Plus.Q.map
        ((singleImageIso F X).inv ≫ F.mapCochainComplexPlus.map (augmentationPlus I)) := by
  have h := F.rightDerivedFunctorPlusUnit.naturality (augmentationPlus I)
  simp only [Functor.comp_map] at h
  have h' : (singlePlusIso X).inv ≫ (singleIsoOfResolution I).hom =
      DerivedCategory.Plus.Q.map (augmentationPlus I) := by
    rw [← singlePlusIso_comp_augmentation I, Iso.inv_hom_id_assoc]
  simp only [zeroUnit, derivedComplexIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_inv, Category.assoc]
  rw [← Functor.map_comp_assoc, h', ← reassoc_of% h]
  simp only [IsIso.hom_inv_id, Category.comp_id, Functor.map_comp]

def qHomologyIso (K : CochainComplex.Plus D) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D n).obj (DerivedCategory.Plus.Q.obj K) ≅
      K.obj.homology n :=
  (DerivedCategory.homologyFunctor D n).mapIso
      ((DerivedCategory.Plus.QCompιIso D).app K) ≪≫
    (DerivedCategory.homologyFunctorFactors D n).app K.obj

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma qHomologyIso_hom_naturality {K L : CochainComplex.Plus D} (f : K ⟶ L) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor D n).map (DerivedCategory.Plus.Q.map f) ≫
        (qHomologyIso L n).hom =
      (qHomologyIso K n).hom ≫ HomologicalComplex.homologyMap f.hom n := by
  have h₁ := (DerivedCategory.Plus.QCompιIso D).hom.naturality f
  have h₂ := (DerivedCategory.homologyFunctorFactors D n).hom.naturality f.hom
  simp only [Functor.comp_map] at h₁ h₂
  simp only [qHomologyIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  change (DerivedCategory.homologyFunctor D n).map
    (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map f)) ≫ _ = _
  rw [← Functor.map_comp_assoc, h₁, Functor.map_comp, Category.assoc]
  simp only [Category.assoc]
  exact congrArg (_ ≫ ·) h₂

omit [HasDerivedCategory D] in
set_option backward.isDefEq.respectTransparency false in
lemma single_homology_extend_zero (A : D) (K : CochainComplex D ℕ)
    (α : (CochainComplex.singleFunctor D 0).obj A ⟶
      K.extend ComplexShape.embeddingUpNat)
    (a : A ⟶ K.cycles 0)
    (ha : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).inv ≫
        α.f 0 ≫ (K.extendXIso ComplexShape.embeddingUpNat (i' := (0 : ℤ)) rfl).hom =
      a ≫ K.iCycles 0) :
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 A).inv ≫
        HomologicalComplex.homologyMap α 0 ≫
        (K.extendHomologyIso ComplexShape.embeddingUpNat (j' := (0 : ℤ)) rfl).hom =
      a ≫ K.homologyπ 0 := by
  rw [← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ]
  simp only [Category.assoc]
  rw [HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_extendHomologyIso_hom]
  simp only [← Category.assoc]
  congr 1
  apply (cancel_mono (K.iCycles 0)).mp
  simp only [Category.assoc, HomologicalComplex.extendCyclesIso_hom_iCycles,
    HomologicalComplex.cyclesMap_i_assoc,
    HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles_assoc]
  exact ha

omit [HasDerivedCategory C] [EnoughInjectives C] [HasDerivedCategory D] in
lemma mapExtendIso_inv_f_comp_extendXIso {ι ι' : Type*} {c : ComplexShape ι}
    {c' : ComplexShape ι'} (K : HomologicalComplex C c) (e : c.Embedding c')
    {i : ι} {i' : ι'} (hi : e.f i = i') :
    (mapExtendIso F K e).inv.f i' ≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e hi).hom =
      F.map (K.extendXIso e hi).hom := by
  have aux (j : Option ι) (hj : j = some i) :
      (extendXMapIso F K j).inv ≫
        (HomologicalComplex.extend.XIso ((F.mapHomologicalComplex c).obj K) hj).hom =
      F.map (HomologicalComplex.extend.XIso K hj).hom := by
    subst hj
    dsimp [extendXMapIso, HomologicalComplex.extend.XIso, HomologicalComplex.extend.X]
    change 𝟙 (F.obj (K.X i)) ≫ 𝟙 _ = F.map (𝟙 (K.X i))
    simp
  change (extendXMapIso F K (e.r i')).inv ≫
    (HomologicalComplex.extend.XIso _ (e.r_eq_some hi)).hom =
      F.map (HomologicalComplex.extend.XIso K (e.r_eq_some hi)).hom
  exact aux _ _

def zeroUnitHomology (X : C) :
    F.obj X ⟶ (DerivedCategory.Plus.homologyFunctor D 0).obj ((derivedComplex F).obj X) :=
  (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (F.obj X)).inv ≫
    (qHomologyIso (singlePlus (F.obj X)) 0).inv ≫
      (DerivedCategory.Plus.homologyFunctor D 0).map (zeroUnit F X)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma zeroUnitHomology_comp_homologyResolutionIso {X : C} (I : InjectiveResolution X) :
    zeroUnitHomology F X ≫ (homologyResolutionIso F I 0).hom =
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (F.obj X)).inv ≫
        HomologicalComplex.homologyMap
          ((singleImageIso F X).inv.hom ≫
            (F.mapHomologicalComplex (ComplexShape.up ℤ)).map I.ι') 0 := by
  simp only [zeroUnitHomology, homologyResolutionIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  change (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (F.obj X)).inv ≫
    (qHomologyIso (singlePlus (F.obj X)) 0).inv ≫
      (DerivedCategory.Plus.homologyFunctor D 0).map (zeroUnit F X) ≫
        (DerivedCategory.Plus.homologyFunctor D 0).map (derivedComplexIso F I).hom ≫
          (qHomologyIso (F.mapCochainComplexPlus.obj (resolutionPlus I)) 0).hom = _
  rw [← Functor.map_comp_assoc, zeroUnit_comp_derivedComplexIso,
    qHomologyIso_hom_naturality, Iso.inv_hom_id_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma zeroUnitHomology_comp_homologyIso {X : C} (I : InjectiveResolution X) :
    zeroUnitHomology F X ≫ (homologyIso F I 0).hom = F.toRightDerivedZero.app X := by
  let α : (CochainComplex.singleFunctor D 0).obj (F.obj X) ⟶
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
        ComplexShape.embeddingUpNat :=
    (singleImageIso F X).inv.hom ≫
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).map I.ι' ≫
        (mapExtendIso F I.cocomplex ComplexShape.embeddingUpNat).inv
  have hα :
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (F.obj X)).inv ≫
        α.f 0 ≫
          (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extendXIso
            ComplexShape.embeddingUpNat (i' := (0 : ℤ)) rfl).hom =
      I.toRightDerivedZero' F ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).iCycles 0 := by
    dsimp [α]
    simp only [Category.assoc]
    rw [mapExtendIso_inv_f_comp_extendXIso]
    simp only [singleImageIso, ObjectProperty.isoMk, ObjectProperty.homMk, Iso.app_inv,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      InjectiveResolution.ι'_f_zero, Category.assoc,
      Iso.inv_hom_id_assoc, ← Functor.map_comp, InjectiveResolution.cochainComplexXIso,
      Iso.inv_hom_id, Category.comp_id,
      InjectiveResolution.toRightDerivedZero'_comp_iCycles]
  have h := single_homology_extend_zero (F.obj X)
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
    α (I.toRightDerivedZero' F) hα
  simp only [homologyIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  erw [zeroUnitHomology_comp_homologyResolutionIso_assoc]
  dsimp only [HomologicalComplex.homologyFunctor]
  erw [← HomologicalComplex.homologyMap_comp_assoc]
  simp only [Category.assoc]
  change _ ≫ HomologicalComplex.homologyMap α 0 ≫ _ ≫ _ = _
  rw [reassoc_of% h]
  exact (I.toRightDerivedZero_eq F).symm

omit [HasDerivedCategory C] [EnoughInjectives C] [HasDerivedCategory D] in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma mapExtendIso_hom_f_comp_map_extendXIso {ι ι' : Type*} {c : ComplexShape ι}
    {c' : ComplexShape ι'} (K : HomologicalComplex C c) (e : c.Embedding c')
    {i : ι} {i' : ι'} (hi : e.f i = i') :
    (mapExtendIso F K e).hom.f i' ≫ F.map (K.extendXIso e hi).hom =
      (((F.mapHomologicalComplex c).obj K).extendXIso e hi).hom := by
  rw [← mapExtendIso_inv_f_comp_extendXIso, ← Category.assoc]
  simp only [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f,
    Category.id_comp]

end Langlands.Cohomology.DerivedPlus

open AlgebraicGeometry
open Langlands.Cohomology

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

universe u

attribute [local instance] HasDerivedCategory.standard

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)}

def pullbackAugmentationPlus (h : Y ⟶ X) (M : X.left.Modules) :
    DerivedPlus.singlePlus M ⟶
      (Scheme.Modules.pushforward h.left).mapCochainComplexPlus.obj
        (DerivedPlus.resolutionPlus
          (injectiveResolution ((Scheme.Modules.pullback h.left).obj M))) :=
  ObjectProperty.homMk (pullbackResolutionAugmentation h M)

set_option backward.isDefEq.respectTransparency false in
lemma pullbackDerivedAugmentation_eq_singlePlus (h : Y ⟶ X) (M : X.left.Modules) :
    pullbackDerivedAugmentation h M =
      (DerivedPlus.singlePlusIso M).hom ≫
        DerivedCategory.Plus.Q.map (pullbackAugmentationPlus h M) := by
  apply DerivedCategory.Plus.ι.map_injective
  have hQ := (DerivedCategory.Plus.QCompιIso X.left.Modules).inv.naturality
    (pullbackAugmentationPlus h M)
  simp only [Functor.comp_map] at hQ
  simp only [pullbackDerivedAugmentation, DerivedPlus.singlePlusIso,
    Functor.map_comp, Functor.map_preimage, Functor.preimageIso_hom,
    Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Category.assoc]
  exact congrArg (fun g =>
    (DerivedCategory.Plus.singleFunctorιIso X.left.Modules 0).hom.app M ≫
      (DerivedCategory.singleFunctorIsoCompQ X.left.Modules 0).hom.app M ≫ g) hQ

set_option backward.isDefEq.respectTransparency false in
lemma pullbackResolutionAugmentation_head (h : Y ⟶ X) (M : X.left.Modules) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv ≫
        (pullbackResolutionAugmentation h M).f 0 ≫
          (Scheme.Modules.pushforward h.left).map
            ((injectiveResolution ((Scheme.Modules.pullback h.left).obj M)).cochainComplexXIso
              0 0 rfl).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction h.left).unit.app M ≫
        (Scheme.Modules.pushforward h.left).map
          ((injectiveResolution ((Scheme.Modules.pullback h.left).obj M)).ι.f 0) := by
  simp only [pullbackResolutionAugmentation, HomologicalComplex.comp_f, Category.assoc,
    InjectiveResolution.cochainComplexXIso]
  rw [DerivedPlus.mapExtendIso_hom_f_comp_map_extendXIso]
  rw [HomologicalComplex.extendSingleIso_inv_f,
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0)
      (i' := (0 : ℤ)) rfl]
  simp only [HomologicalComplex.comp_f, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id, AcyclicResolution.mapAugmentation_f_zero,
    CochainComplex.single₀_map_f_zero]
  erw [Iso.inv_hom_id_assoc]
  change 𝟙 M ≫ _ ≫ (Scheme.Modules.pushforward h.left).map (𝟙 _ ≫ _) = _
  simp only [Category.id_comp]

def pullbackSectionsAugmentationPlus (h : Y ⟶ X) (M : X.left.Modules) :
    DerivedPlus.singlePlus ((relativeGlobalSections X.hom).obj M) ⟶
      (relativeGlobalSections Y.hom).mapCochainComplexPlus.obj
        (DerivedPlus.resolutionPlus
          (injectiveResolution ((Scheme.Modules.pullback h.left).obj M))) :=
  (DerivedPlus.singleImageIso (relativeGlobalSections X.hom) M).inv ≫
    (relativeGlobalSections X.hom).mapCochainComplexPlus.map
      (pullbackAugmentationPlus h M) ≫
    (pullbackSectionsComplexIso h
      (DerivedPlus.resolutionPlus
        (injectiveResolution ((Scheme.Modules.pullback h.left).obj M)))).hom

set_option backward.isDefEq.respectTransparency false in
lemma zeroUnit_comp_relativeDerivedSectionsPullback (h : Y ⟶ X) (M : X.left.Modules) :
    DerivedPlus.zeroUnit (relativeGlobalSections X.hom) M ≫
        relativeDerivedSectionsPullback h M ≫
          (DerivedPlus.derivedComplexIso (relativeGlobalSections Y.hom)
            (injectiveResolution ((Scheme.Modules.pullback h.left).obj M))).hom =
      DerivedCategory.Plus.Q.map (pullbackSectionsAugmentationPlus h M) := by
  let I := injectiveResolution ((Scheme.Modules.pullback h.left).obj M)
  let K := DerivedPlus.resolutionPlus I
  let L := (Scheme.Modules.pushforward h.left).mapCochainComplexPlus.obj K
  have hL (i : ℤ) (q : ℕ) :
      IsZero (((relativeGlobalSections X.hom).rightDerived (q + 1)).obj (L.obj.X i)) :=
    (pushforwardInjectiveAcyclic Y.left X.left h.left (K.obj.X i)
      inferInstance q).2 R X.hom
  have := acyclicTermsDerivedUnitStatement X.left.Modules (ModuleCat.{u} R)
    (relativeGlobalSections X.hom) L hL
  have hn := (relativeGlobalSections X.hom).rightDerivedFunctorPlusUnit.naturality
    (pullbackAugmentationPlus h M)
  simp only [Functor.comp_map] at hn
  simp only [DerivedPlus.zeroUnit, relativeDerivedSectionsPullback,
    pullbackSectionsAugmentationPlus, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [pullbackDerivedAugmentation_eq_singlePlus, Functor.map_comp]
  simp only [Category.assoc]
  erw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [← reassoc_of% hn]
  simp only [IsIso.hom_inv_id_assoc, Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma zeroUnitHomology_comp_pullback_homologyResolutionIso
    (h : Y ⟶ X) (M : X.left.Modules) :
    DerivedPlus.zeroUnitHomology (relativeGlobalSections X.hom) M ≫
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
          (relativeDerivedSectionsPullback h M) ≫
        (DerivedPlus.homologyResolutionIso (relativeGlobalSections Y.hom)
          (injectiveResolution ((Scheme.Modules.pullback h.left).obj M)) 0).hom =
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
        ((relativeGlobalSections X.hom).obj M)).inv ≫
        HomologicalComplex.homologyMap (pullbackSectionsAugmentationPlus h M).hom 0 := by
  simp only [DerivedPlus.zeroUnitHomology, DerivedPlus.homologyResolutionIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  change (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
      ((relativeGlobalSections X.hom).obj M)).inv ≫
    (DerivedPlus.qHomologyIso
      (DerivedPlus.singlePlus ((relativeGlobalSections X.hom).obj M)) 0).inv ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
        (DerivedPlus.zeroUnit (relativeGlobalSections X.hom) M) ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
        (relativeDerivedSectionsPullback h M) ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
        (DerivedPlus.derivedComplexIso (relativeGlobalSections Y.hom)
          (injectiveResolution ((Scheme.Modules.pullback h.left).obj M))).hom ≫
      (DerivedPlus.qHomologyIso
        ((relativeGlobalSections Y.hom).mapCochainComplexPlus.obj
          (DerivedPlus.resolutionPlus
            (injectiveResolution ((Scheme.Modules.pullback h.left).obj M)))) 0).hom = _
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [zeroUnit_comp_relativeDerivedSectionsPullback,
    DerivedPlus.qHomologyIso_hom_naturality, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
lemma pullbackSectionsComplexIso_hom_f (h : Y ⟶ X)
    (K : CochainComplex.Plus Y.left.Modules) (n : ℤ) :
    (pullbackSectionsComplexIso h K).hom.hom.f n =
      (relativePushforwardSectionsIso h).hom.app (K.obj.X n) := by
  change ((CochainComplex.Plus.ι _).map (pullbackSectionsComplexIso h K).hom).f n = _
  simp only [pullbackSectionsComplexIso, Functor.preimageIso_hom, Functor.map_preimage]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma pullbackSectionsAugmentationPlus_head (h : Y ⟶ X) (M : X.left.Modules) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        ((relativeGlobalSections X.hom).obj M)).inv ≫
      (pullbackSectionsAugmentationPlus h M).hom.f 0 ≫
        (relativeGlobalSections Y.hom).map
          ((injectiveResolution ((Scheme.Modules.pullback h.left).obj M)).cochainComplexXIso
            0 0 rfl).hom =
      relativeGlobalSectionsPullback h M ≫
        (relativeGlobalSections Y.hom).map
          ((injectiveResolution ((Scheme.Modules.pullback h.left).obj M)).ι.f 0) := by
  let I := injectiveResolution ((Scheme.Modules.pullback h.left).obj M)
  have hs := (relativePushforwardSectionsIso h).hom.naturality
    (I.cochainComplexXIso 0 0 rfl).hom
  have hι := (relativePushforwardSectionsIso h).hom.naturality (I.ι.f 0)
  simp only [Functor.comp_map] at hs hι
  simp only [pullbackSectionsAugmentationPlus, ObjectProperty.FullSubcategory.comp_hom,
    HomologicalComplex.comp_f, pullbackSectionsComplexIso_hom_f, Category.assoc]
  change (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      ((relativeGlobalSections X.hom).obj M)).inv ≫
    (DerivedPlus.singleImageIso (relativeGlobalSections X.hom) M).inv.hom.f 0 ≫
      (relativeGlobalSections X.hom).map ((pullbackResolutionAugmentation h M).f 0) ≫
      (relativePushforwardSectionsIso h).hom.app (I.cochainComplex.X 0) ≫
    (relativeGlobalSections Y.hom).map (I.cochainComplexXIso 0 0 rfl).hom = _
  rw [← hs]
  simp only [DerivedPlus.singleImageIso, ObjectProperty.isoMk, ObjectProperty.homMk,
    Iso.app_inv, HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [pullbackResolutionAugmentation_head]
  simp only [Functor.map_comp, Category.assoc, relativeGlobalSectionsPullback]
  exact congrArg (_ ≫ ·) hι

set_option backward.isDefEq.respectTransparency false in
lemma zeroUnitHomology_comp_pullback_homologyIso (h : Y ⟶ X) (M : X.left.Modules) :
    DerivedPlus.zeroUnitHomology (relativeGlobalSections X.hom) M ≫
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
          (relativeDerivedSectionsPullback h M) ≫
        (DerivedPlus.homologyIso (relativeGlobalSections Y.hom)
          (injectiveResolution ((Scheme.Modules.pullback h.left).obj M)) 0).hom =
      relativeGlobalSectionsPullback h M ≫
        (relativeGlobalSections Y.hom).toRightDerivedZero.app
          ((Scheme.Modules.pullback h.left).obj M) := by
  let G := relativeGlobalSections Y.hom
  let I := injectiveResolution ((Scheme.Modules.pullback h.left).obj M)
  let α : (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((relativeGlobalSections X.hom).obj M) ⟶
      ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
        ComplexShape.embeddingUpNat :=
    (pullbackSectionsAugmentationPlus h M).hom ≫
      (DerivedPlus.mapExtendIso G I.cocomplex ComplexShape.embeddingUpNat).inv
  have hα :
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          ((relativeGlobalSections X.hom).obj M)).inv ≫
        α.f 0 ≫
          (((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extendXIso
            ComplexShape.embeddingUpNat (i' := (0 : ℤ)) rfl).hom =
      (relativeGlobalSectionsPullback h M ≫ I.toRightDerivedZero' G) ≫
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).iCycles 0 := by
    dsimp [α]
    simp only [Category.assoc]
    rw [DerivedPlus.mapExtendIso_inv_f_comp_extendXIso]
    erw [pullbackSectionsAugmentationPlus_head]
    simp only [InjectiveResolution.toRightDerivedZero'_comp_iCycles]
    rfl
  have hZero := DerivedPlus.single_homology_extend_zero
    ((relativeGlobalSections X.hom).obj M)
    ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
    α (relativeGlobalSectionsPullback h M ≫ I.toRightDerivedZero' G) hα
  simp only [DerivedPlus.homologyIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  erw [zeroUnitHomology_comp_pullback_homologyResolutionIso_assoc]
  dsimp only [HomologicalComplex.homologyFunctor]
  erw [← HomologicalComplex.homologyMap_comp_assoc]
  change _ ≫ HomologicalComplex.homologyMap α 0 ≫ _ ≫ _ = _
  rw [reassoc_of% hZero]
  exact congrArg (relativeGlobalSectionsPullback h M ≫ ·) (I.toRightDerivedZero_eq G).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma toRightDerivedZero_comp_relativeCohomologyPullback
    (h : Y ⟶ X) (M : X.left.Modules) :
    (relativeGlobalSections X.hom).toRightDerivedZero.app M ≫
        relativeCohomologyPullback h M 0 =
      relativeGlobalSectionsPullback h M ≫
        (relativeGlobalSections Y.hom).toRightDerivedZero.app
          ((Scheme.Modules.pullback h.left).obj M) := by
  rw [← DerivedPlus.zeroUnitHomology_comp_homologyIso
    (relativeGlobalSections X.hom) (injectiveResolution M)]
  simp only [relativeCohomologyPullback, Category.assoc, Iso.hom_inv_id_assoc]
  exact zeroUnitHomology_comp_pullback_homologyIso h M

set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero canonical pullback is the actual pullback on relative sections. -/
theorem relativeCohomologyPullbackDegreeZeroStatement :
    RelativeCohomologyPullbackDegreeZeroStatement.{u} := by
  intro R X Y h M
  apply (cancel_epi ((relativeGlobalSections X.hom).toRightDerivedZero.app M)).mp
  change (relativeGlobalSections X.hom).toRightDerivedZero.app M ≫
      (relativeCohomologyPullback h M 0 ≫
        (relativeGlobalSections Y.hom).rightDerivedZeroIsoSelf.hom.app _) =
    (relativeGlobalSections X.hom).toRightDerivedZero.app M ≫
      ((relativeGlobalSections X.hom).rightDerivedZeroIsoSelf.hom.app M ≫
        relativeGlobalSectionsPullback h M)
  erw [toRightDerivedZero_comp_relativeCohomologyPullback_assoc]
  simp only [Functor.rightDerivedZeroIsoSelf_inv_hom_id_app,
    Functor.rightDerivedZeroIsoSelf_inv_hom_id_app_assoc, Category.comp_id]

end Langlands.AlgebraicGeometry.Modules.DerivedSections
