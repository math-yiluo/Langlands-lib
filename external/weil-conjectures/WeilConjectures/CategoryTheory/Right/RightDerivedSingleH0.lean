/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# The zeroth homology of the single-object right-derived unit

Source: Stacks Project, Tag 05TD. This is the generic augmentation calculation used
for the direct-image specialization in `CanonicalDirectImageH0Unit`.
-/

@[expose] public section

set_option autoImplicit false
open CategoryTheory Limits
noncomputable section

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open Abelian in
private theorem unit_plus {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] [HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (M : C) :
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.singleFunctor C 0).obj M) ≫
      (F.rightDerivedFunctorPlusCompatibility.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj M)).inv =
    DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor C 0).obj M)) := by
  apply (Iso.comp_inv_eq _).2
  have h := (Functor.rightDerivedNatTrans_app
      (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
      (DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor)
      F.rightDerivedFunctorPlusιUnit F.ιRightDerivedFunctorUnit
      (HomotopyCategory.Plus.quasiIso C) (𝟙 _)
      ((HomotopyCategory.Plus.singleFunctor C 0).obj M)).symm
  simp only [NatTrans.id_app, Category.id_comp] at h
  change F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.Plus.singleFunctor C 0).obj M).obj =
    DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor C 0).obj M)) ≫
    (F.rightDerivedFunctorPlusCompatibility.app
      (DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.singleFunctor C 0).obj M))).hom at h
  exact h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open Abelian in
private theorem plus_unit_resolution {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] (M : C) :
    F.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.singleFunctor C 0).obj M) ≫
      (F.rightDerivedFunctorPlusObjSingleFunctorIsoQ M).hom =
    DerivedCategory.Plus.Q.map (ObjectProperty.homMk
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (injectiveResolution M).ι') :
        ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor C 0).obj M), 0, inferInstance⟩ ⟶
        F.rightDerivedPlusComplex M) := by
  let R := injectiveResolution M
  let K : CochainComplex.Plus C :=
    ⟨(CochainComplex.singleFunctor C 0).obj M, 0, inferInstance⟩
  let L : CochainComplex.Plus C := ⟨R.cochainComplex, 0, inferInstance⟩
  let g : K ⟶ L := ObjectProperty.homMk R.ι'
  have h := F.rightDerivedFunctorPlusUnith.naturality
    ((HomotopyCategory.Plus.quotient C).map g)
  dsimp only [Functor.comp_map] at h
  unfold Functor.rightDerivedFunctorPlusObjSingleFunctorIsoQ
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv]
  have : ∀ n, Injective (L.obj.X n) := fun n ↦
    inferInstanceAs (Injective (R.cochainComplex.X n))
  let qC := (DerivedCategory.Plus.quotientCompQhIso C).app L
  have he : (DerivedCategory.Plus.ι.preimageIso
      (X := (DerivedCategory.Plus.singleFunctor C 0).obj M)
      (Y := DerivedCategory.Plus.Q.obj L)
      ((DerivedCategory.singleFunctorIsoCompQ C 0).app M ≪≫
        asIso (DerivedCategory.Q.map R.ι'))).hom =
      DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map g) ≫ qC.hom := by
    apply DerivedCategory.Plus.ι.map_injective
    simp only [Functor.preimageIso_hom, Functor.map_preimage, Iso.trans_hom, Functor.map_comp]
    dsimp [qC, DerivedCategory.singleFunctorIsoCompQ, DerivedCategory.quotientCompQhIso,
      DerivedCategory.Plus.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso]
    erw [Category.id_comp, Category.comp_id]
    rfl
  rw [he, Functor.map_comp]
  have h' : F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor C 0).obj M) ≫
      F.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map g)) =
    DerivedCategory.Plus.Qh.map (F.mapHomotopyCategoryPlus.map
      ((HomotopyCategory.Plus.quotient C).map g)) ≫
      F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient C).obj L) := h.symm
  simp only [Category.assoc]
  rw [reassoc_of% h']
  have : IsIso (F.rightDerivedFunctorPlusUnit.app L) := by
    let L' : CochainComplex (InjectiveObject C) ℤ :=
      HomologicalComplex.liftObjectProperty _ R.cochainComplex inferInstance
    have hL' : L'.IsStrictlyGE 0 := by
      rw [← CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ (InjectiveObject.ι C)]
      exact inferInstanceAs (R.cochainComplex.IsStrictlyGE 0)
    exact inferInstanceAs (IsIso (F.rightDerivedFunctorPlusUnit.app
      ((InjectiveObject.ι C).mapCochainComplexPlus.obj ⟨L', 0, hL'⟩)))
  rw [← cancel_mono (F.rightDerivedFunctorPlusUnit.app L)]
  simp only [Category.assoc]
  erw [IsIso.inv_hom_id, Category.comp_id]
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (F.rightDerivedFunctorPlusUnit_app L).symm)
  have key : DerivedCategory.Plus.Qh.map (F.mapHomotopyCategoryPlus.map
      ((HomotopyCategory.Plus.quotient C).map g)) =
      DerivedCategory.Plus.Q.map (ObjectProperty.homMk
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (injectiveResolution M).ι') :
          ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((CochainComplex.singleFunctor C 0).obj M), 0, inferInstance⟩ ⟶
          F.rightDerivedPlusComplex M) ≫
        (DerivedCategory.Plus.quotientCompQhIso D).inv.app (F.mapCochainComplexPlus.obj L) ≫
        DerivedCategory.Plus.Qh.map (F.quotientCompMapHomotopyCategoryPlusIso.inv.app L) := by
    apply DerivedCategory.Plus.ι.map_injective
    simp only [Functor.map_comp]
    dsimp [DerivedCategory.quotientCompQhIso, DerivedCategory.Plus.quotientCompQhIso,
      HomologicalComplexUpToQuasiIso.quotientCompQhIso,
      Functor.quotientCompMapHomotopyCategoryPlusIso]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, ObjectProperty.FullSubcategory.id_hom,
      Category.comp_id]
    rfl
  refine Eq.trans (congrArg (· ≫ _) key) ?_
  simp only [Category.assoc]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open Abelian in
private theorem unit_homology_resolution {C D : Type*}
    [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] [HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (M : C) (n : ℕ) :
    (DerivedCategory.homologyFunctor D n).map
        (F.rightDerivedFunctorUnit.app ((HomotopyCategory.singleFunctor C 0).obj M)) ≫
      (F.homologyRightDerivedFunctorObjSingleFunctorIso M n).hom =
    ((DerivedCategory.homologyFunctorFactorsh D n).app _ ≪≫
      (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) n).app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor C 0).obj M))).hom ≫
      HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (injectiveResolution M).ι') n ≫
      ((injectiveResolution M).isoRightDerivedObjCochainComplex F n).inv := by
  let K : CochainComplex.Plus D :=
    ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor C 0).obj M), 0, inferInstance⟩
  let g : K ⟶ F.rightDerivedPlusComplex M := ObjectProperty.homMk
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (injectiveResolution M).ι')
  dsimp only [Functor.homologyRightDerivedFunctorObjSingleFunctorIso,
    Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, unit_plus]
  change (DerivedCategory.Plus.homologyFunctor D n).map
      (F.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.singleFunctor C 0).obj M)) ≫ _ = _
  rw [← Functor.map_comp_assoc, plus_unit_resolution]
  have h := DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality g n
  change (DerivedCategory.Plus.homologyFunctor D n).map
      (DerivedCategory.Plus.Q.map g) ≫ _ = _
  erw [reassoc_of% h]
  dsimp only [DerivedCategory.Plus.homologyFunctorObjQIso, Iso.app_hom, Iso.trans_hom]
  rw [DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [show (DerivedCategory.quotientCompQhIso D).hom.app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor C 0).obj M)) = 𝟙 _ from rfl,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open Abelian in
private theorem augmentation_homology {C D : Type*}
    [Category C] [Category D] [Abelian C] [Abelian D]
    [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] (M : C) :
    HomologicalComplex.homologyMap
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app M ≫
          (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (injectiveResolution M).ι') 0 ≫
      ((injectiveResolution M).isoRightDerivedObjCochainComplex F 0).inv =
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (F.obj M)).hom ≫
      F.toRightDerivedZero.app M := by
  let R := injectiveResolution M
  let K := (CochainComplex.singleFunctor D 0).obj (F.obj M)
  let g := (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app M ≫
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.ι'
  change HomologicalComplex.homologyMap g 0 ≫
    (R.isoRightDerivedObjCochainComplex F 0).inv =
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (F.obj M)).hom ≫
      F.toRightDerivedZero.app M
  rw [R.toRightDerivedZero_eq F]
  dsimp only [InjectiveResolution.isoRightDerivedObjCochainComplex, Iso.trans_inv,
    Functor.mapIso_inv, Iso.symm_inv]
  simp only [Category.assoc]
  rw [← cancel_mono (R.isoRightDerivedObj F 0).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [HomologicalComplex.homologyFunctor_map]
  rw [← cancel_epi (K.homologyπ 0)]
  change K.homologyπ 0 ≫ HomologicalComplex.homologyMap g 0 ≫ _ = _
  dsimp [K]
  erw [HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom_assoc]
  erw [HomologicalComplex.homologyπ_extendHomologyIso_hom]
  change HomologicalComplex.cyclesMap g 0 ≫
      HomologicalComplex.cyclesMap (R.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F).hom 0 ≫
      (((F.mapHomologicalComplex _).obj R.cocomplex).extendCyclesIso
        ComplexShape.embeddingUpNat rfl).hom ≫
      ((F.mapHomologicalComplex _).obj R.cocomplex).homologyπ 0 = _
  have hc : HomologicalComplex.cyclesMap g 0 ≫
      HomologicalComplex.cyclesMap (R.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F).hom 0 ≫
      (((F.mapHomologicalComplex _).obj R.cocomplex).extendCyclesIso
        ComplexShape.embeddingUpNat rfl).hom =
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 (F.obj M)).hom ≫
        R.toRightDerivedZero' F := by
    apply (cancel_mono (((F.mapHomologicalComplex _).obj R.cocomplex).iCycles 0)).1
    simp only [Category.assoc, HomologicalComplex.extendCyclesIso_hom_iCycles,
      InjectiveResolution.toRightDerivedZero'_comp_iCycles]
    erw [HomologicalComplex.cyclesMap_i_assoc, HomologicalComplex.cyclesMap_i_assoc]
    dsimp [g]
    change K.iCycles 0 ≫ g.f 0 ≫
      (R.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F).hom.f 0 ≫
      (((F.mapHomologicalComplex _).obj R.cocomplex).extendXIso
        ComplexShape.embeddingUpNat rfl).hom = _
    dsimp only [g]
    erw [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      InjectiveResolution.ι'_f_zero]
    simp only [Functor.map_comp, Category.assoc]
    simp only [← F.map_comp_assoc]
    have hm : (R.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F).hom.f 0 ≫
        (((F.mapHomologicalComplex _).obj R.cocomplex).extendXIso
          ComplexShape.embeddingUpNat rfl).hom =
        F.map (R.cochainComplexXIso 0 0 rfl).hom := by
      simp only [InjectiveResolution.cochainComplexXIso, HomologicalComplex.mapExtendIso,
        HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso,
        Functor.mapHomologicalComplex_obj_X, ComplexShape.embeddingUpNat_f,
        Int.cast_ofNat_Int, HomologicalComplex.Hom.isoOfComponents_hom_f]
      have hr : ComplexShape.embeddingUpNat.r (0 : ℤ) = some (0 : ℕ) :=
        ComplexShape.embeddingUpNat.r_f 0
      erw [HomologicalComplex.mapExtendX_hom_eq R.cocomplex F hr]
      erw [eqToHom_map]
      · simp only [eqToIso.hom, eqToHom_trans]
      · change HomologicalComplex.extend.X R.cocomplex
          (ComplexShape.embeddingUpNat.r 0) = R.cocomplex.X 0
        rw [hr]
        rfl
    erw [hm]
    erw [← F.map_comp]
    have hh : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).hom ≫
        R.ι.f 0 ≫ (R.cochainComplexXIso 0 0 rfl).inv) ≫
        (R.cochainComplexXIso 0 0 rfl).hom = R.ι.f 0 := by
      simp
    erw [hh]
    exact (Category.assoc _ _ _).symm
  rw [reassoc_of% hc]

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

variable [Abelian.HasKInjectiveResolutions C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical augmentation from `F M[0]` to `RF(M[0])`, natural in `M`.
Source: Stacks Project, Tag 05TD (blueprint: lem-kun-right-derived-single-h0). -/
@[no_expose] def singleRightDerivedUnit (F : C ⥤ D) [F.Additive] :
    F ⋙ DerivedCategory.singleFunctor D 0 ⟶
      DerivedCategory.singleFunctor C 0 ⋙ F.rightDerivedFunctor where
  app M := DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) ≫
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.singleFunctor C 0).obj M)
  naturality M N f := by
    have hs := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.naturality f
    have hu := F.rightDerivedFunctorUnit.naturality
      ((HomotopyCategory.singleFunctor C 0).map f)
    dsimp only [Functor.comp_map] at hu hs
    change DerivedCategory.Q.map ((HomologicalComplex.single D (.up ℤ) 0).map (F.map f)) ≫
      _ ≫ _ = _
    erw [← DerivedCategory.Q.map_comp_assoc, hs, DerivedCategory.Q.map_comp,
      Category.assoc]
    simp only [Category.assoc]
    apply congrArg (fun g ↦ DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) ≫ g)
    exact hu

/-- The canonical unit is the localized single-complex comparison followed by the derived unit.
Source: Stacks Tag 05TD (blueprint: lem-kun-right-derived-single-h0).
Proof: this is the defining formula of the canonical natural transformation. -/
theorem singleRightDerivedUnit_app (F : C ⥤ D) [F.Additive] (M : C) :
    F.singleRightDerivedUnit.app M =
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) ≫
      cast (by rfl)
        (F.rightDerivedFunctorUnit.app ((HomotopyCategory.singleFunctor C 0).obj M)) := by
  rw [cast_eq]
  rfl

/-- The canonical zeroth-homology identification for a left exact functor.
Source: Stacks Tag 05TD (blueprint: lem-kun-right-derived-single-h0). -/
@[no_expose, irreducible] def singleRightDerivedH0Iso (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F]
    [EnoughInjectives C] (M : C) :
    (DerivedCategory.homologyFunctor D 0).obj
        (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj M)) ≅ F.obj M :=
  F.homologyRightDerivedFunctorObjSingleFunctorIso M 0 ≪≫ F.rightDerivedZeroIsoSelf.app M

end CategoryTheory.Functor

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open Abelian in
/-- The canonical map from the single object of `F M` to `RF(M[0])` is inverse on H⁰
 to the canonical left-exact zeroth-derived identification.

Source: Stacks Project, Tag 05TD, lemma-left-exact-higher-derived (3).
(blueprint: lem-kun-right-derived-single-h0).

Proof: compare the unbounded right-derived unit with its bounded-below unit by
uniqueness of right derived functors. Naturality on the injective-resolution
augmentation computes its homology as the classical map `toRightDerivedZero`.
The single-complex comparison cancels the single-map comparison in that computation.
Left exactness makes `toRightDerivedZero` inverse to `rightDerivedZeroIsoSelf`,
and the remaining map is the canonical single-complex homology identification.
The construction also applies to zero objects and zero functors. -/
theorem CategoryTheory.Functor.rightDerivedFunctorUnit_homology_zero
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] (M : C) :
    (DerivedCategory.homologyFunctor D 0).map (F.singleRightDerivedUnit.app M) ≫
      (F.singleRightDerivedH0Iso M).hom =
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).app (F.obj M)).hom := by
  delta Functor.singleRightDerivedH0Iso
  let H := DerivedCategory.homologyFunctor D 0
  let a := (HomologicalComplex.singleMapHomologicalComplex F
    (ComplexShape.up ℤ) 0).inv.app M
  have h := unit_homology_resolution F M 0
  have h' := augmentation_homology F M
  change H.map (DerivedCategory.Q.map a ≫
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.singleFunctor C 0).obj M)) ≫
      (F.homologyRightDerivedFunctorObjSingleFunctorIso M 0 ≪≫
        F.rightDerivedZeroIsoSelf.app M).hom = _
  simp only [Functor.map_comp, Iso.trans_hom, Category.assoc]
  erw [reassoc_of% h]
  have hn := (DerivedCategory.homologyFunctorFactorsh D 0).hom.naturality
    ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map a)
  have hn' := (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) 0).hom.naturality a
  dsimp only [Functor.comp_map] at hn hn'
  simp only [Iso.trans_hom, Category.assoc]
  erw [reassoc_of% hn, reassoc_of% hn']
  erw [← HomologicalComplex.homologyMap_comp_assoc, reassoc_of% h']
  erw [Functor.rightDerivedZeroIsoSelf_inv_hom_id_app, Category.comp_id]
  erw [DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  erw [show (DerivedCategory.quotientCompQhIso D).hom.app
      ((HomologicalComplex.single D (ComplexShape.up ℤ) 0).obj (F.obj M)) = 𝟙 _ from rfl,
    CategoryTheory.Functor.map_id, Category.id_comp]
  dsimp [DerivedCategory.singleFunctorCompHomologyFunctorIso]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
