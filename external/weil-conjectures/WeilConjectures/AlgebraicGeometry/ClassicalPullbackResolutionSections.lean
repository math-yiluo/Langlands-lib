/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import all Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.CategoryTheory.ResolutionPullbackAugmentation
import WeilConjectures.CategoryTheory.IdentityDerivedHomologyComparison

/-! # Pullback computed on a comparison of injective resolutions -/

@[expose] public section

universe u
open CategoryTheory Limits
namespace CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem resolution_baseChange_unit
    {A A' D : Type*} [Category* A] [Category* A'] [Category* D]
    [Abelian A] [Abelian A'] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory A'] [HasDerivedCategory D]
    [EnoughInjectives A] [EnoughInjectives A']
    (F : A ⥤ D) (F' : A' ⥤ D) (L : A ⥤ A')
    [F.Additive] [F'.Additive] [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (η : F ⟶ L ⋙ F') (K : HomotopyCategory.Plus A) :
    F.rightDerivedFunctorPlusUnith.app K ≫
        (mapDerivedCategoryPlusIdIso D).inv.app
          (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) ≫
        (rightDerivedFunctorPlusBaseChange ((rightUnitor F).hom ≫ η)).app
          (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus η).app K) ≫
        DerivedCategory.Plus.Qh.map
          ((mapHomotopyCategoryPlusCompIso (Iso.refl (L ⋙ F'))).inv.app K) ≫
        F'.rightDerivedFunctorPlusUnith.app (L.mapHomotopyCategoryPlus.obj K) ≫
        F'.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.inv.app K) := by
  have h := congr_app
    (rightDerivedFunctorPlusBaseChange_fac ((rightUnitor F).hom ≫ η)) K
  simp only [NatTrans.comp_app, whiskerRight_app, associator_hom_app, Category.comp_id,
    whiskerLeft_app] at h
  have hn := (mapDerivedCategoryPlusIdIso D).inv.naturality
    (F.rightDerivedFunctorPlusUnith.app K)
  dsimp only [comp_map, id_map] at hn
  erw [← Category.assoc, hn, Category.assoc, h]
  simp only [rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, associator_hom_app, associator_inv_app,
    Category.comp_id, Category.id_comp, mapHomotopyCategoryPlusCompIso_refl_hom_app,
    mapHomotopyCategoryPlusCompIso_refl_inv_app, map_id]
  have hi : (mapDerivedCategoryPlusIdIso D).inv.app
      (DerivedCategory.Plus.Qh.obj (F.mapHomotopyCategoryPlus.obj K)) ≫
      (𝟭 D).mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj K) =
      𝟙 _ := by
    rw [← mapDerivedCategoryPlusIdIso_hom_app_factorsh]
    simp
  erw [← Category.assoc, ← Category.assoc, ← Category.assoc, hi, Category.id_comp]
  erw [Category.id_comp, Category.id_comp, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem resolution_baseChange_sections
    {A A' D : Type*} [Category* A] [Category* A'] [Category* D]
    [Abelian A] [Abelian A'] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory A'] [HasDerivedCategory D]
    [EnoughInjectives A] [EnoughInjectives A']
    (F : A ⥤ D) (F' : A' ⥤ D) (L : A ⥤ A')
    [F.Additive] [F'.Additive] [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (η : F ⟶ L ⋙ F') (G : A) (q : ℕ)
    (φ : (L.mapHomologicalComplex (.up ℤ)).obj
      (injectiveResolution G).cochainComplex ⟶
      (injectiveResolution (L.obj G)).cochainComplex)
    (hφ : Nonempty (Homotopy
      ((L.mapHomologicalComplex (.up ℤ)).map (injectiveResolution G).ι' ≫ φ)
      ((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).hom.app G ≫
        (injectiveResolution (L.obj G)).ι'))) :
    ((injectiveResolution G).isoRightDerivedObjCochainComplex F q).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex η (.up ℤ)).app
            (injectiveResolution G).cochainComplex ≫
            (F'.mapHomologicalComplex (.up ℤ)).map φ) (q : ℤ) =
      (rightDerivedBaseChange ((rightUnitor F).hom ≫ η) q).app G ≫
        ((injectiveResolution (L.obj G)).isoRightDerivedObjCochainComplex F' q).hom := by
  let I : CochainComplex.Plus A :=
    ⟨(injectiveResolution G).cochainComplex, 0, inferInstance⟩
  let J : CochainComplex.Plus A' :=
    ⟨(injectiveResolution (L.obj G)).cochainComplex, 0, inferInstance⟩
  let KI := (HomotopyCategory.Plus.quotient _).obj I
  let KJ := (HomotopyCategory.Plus.quotient _).obj J
  let LI : CochainComplex.Plus A' :=
    ⟨(L.mapHomologicalComplex (.up ℤ)).obj I.obj, 0, inferInstance⟩
  let f : LI ⟶ J := ObjectProperty.homMk φ
  let a := DerivedCategory.Plus.ι.preimageIso
    (X := (DerivedCategory.Plus.singleFunctor _ 0).obj G)
    (Y := DerivedCategory.Plus.Q.obj I)
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app G ≪≫
      asIso (DerivedCategory.Q.map (injectiveResolution G).ι'))
  let a' := DerivedCategory.Plus.ι.preimageIso
    (X := (DerivedCategory.Plus.singleFunctor _ 0).obj (L.obj G))
    (Y := DerivedCategory.Plus.Q.obj J)
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app (L.obj G) ≪≫
      asIso (DerivedCategory.Q.map (injectiveResolution (L.obj G)).ι'))
  let e := (Functor.rightUnitor F).hom ≫ η
  let Z := (DerivedCategory.Plus.singleFunctor _ 0).obj G
  let H := DerivedCategory.Plus.homologyFunctor D (q : ℤ)
  let b : F.rightDerivedPlusComplex G ⟶ F'.rightDerivedPlusComplex (L.obj G) :=
    ObjectProperty.homMk
      ((NatTrans.mapHomologicalComplex η (.up ℤ)).app I.obj ≫
        (F'.mapHomologicalComplex (.up ℤ)).map φ)
  have hqI : (DerivedCategory.quotientCompQhIso A).symm.app I.obj = Iso.refl _ := rfl
  have hqJ : (DerivedCategory.quotientCompQhIso A').symm.app J.obj = Iso.refl _ := rfl
  have ha := Functor.resolution_pullback_augmentation L G φ hφ
  dsimp only at ha
  erw [hqI, hqJ, Iso.trans_refl, Iso.trans_refl] at ha
  change L.mapDerivedCategoryPlus.map a.hom ≫
    L.mapDerivedCategoryPlusFactorsh.hom.app KI ≫ DerivedCategory.Plus.Q.map f =
    (L.mapDerivedCategoryPlusSingleFunctor 0).hom.app G ≫ a'.hom at ha
  have hu := Functor.resolution_baseChange_unit F F' L η KI
  have hrep :
      (Functor.mapDerivedCategoryPlusIdIso _).inv.app (F.rightDerivedFunctorPlus.obj Z) ≫
        (Functor.rightDerivedFunctorPlusBaseChange e).app Z ≫
        F'.rightDerivedFunctorPlus.map ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app G) ≫
        (F'.rightDerivedFunctorPlusObjSingleFunctorIsoQ (L.obj G)).hom =
      (F.rightDerivedFunctorPlusObjSingleFunctorIsoQ G).hom ≫
        DerivedCategory.Plus.Q.map b := by
    have huI : F.rightDerivedFunctorPlusUnit.app I =
        F.rightDerivedFunctorPlusUnith.app KI := by
      erw [rightDerivedFunctorPlusUnit_app]
      change 𝟙 _ ≫ DerivedCategory.Plus.Qh.map (𝟙 _) ≫
        F.rightDerivedFunctorPlusUnith.app KI ≫
        F.rightDerivedFunctorPlus.map (𝟙 _) = _
      erw [Functor.map_id, Functor.map_id, Category.id_comp, Category.id_comp, Category.comp_id]
    have huJ : F'.rightDerivedFunctorPlusUnit.app J =
        F'.rightDerivedFunctorPlusUnith.app KJ := by
      erw [rightDerivedFunctorPlusUnit_app]
      change 𝟙 _ ≫ DerivedCategory.Plus.Qh.map (𝟙 _) ≫
        F'.rightDerivedFunctorPlusUnith.app KJ ≫
        F'.rightDerivedFunctorPlus.map (𝟙 _) = _
      erw [Functor.map_id, Functor.map_id, Category.id_comp, Category.id_comp, Category.comp_id]
    have hn := (Functor.rightDerivedFunctorPlusBaseChange e).naturality a.hom
    have hi := (Functor.mapDerivedCategoryPlusIdIso D).inv.naturality
      (F.rightDerivedFunctorPlus.map a.hom)
    dsimp only [Functor.comp_map, Functor.id_map] at hn hi
    have hf := F'.rightDerivedFunctorPlusUnith.naturality
      ((HomotopyCategory.Plus.quotient A').map f)
    dsimp only [Functor.comp_map] at hf
    simp only [rightDerivedFunctorPlusObjSingleFunctorIsoQ, Iso.trans_hom,
      mapIso_hom, Iso.symm_hom, asIso_inv, Category.assoc]
    have : IsIso (F.rightDerivedFunctorPlusUnit.app I) := by
      rw [huI]
      infer_instance
    have : IsIso (F'.rightDerivedFunctorPlusUnit.app J) := by
      rw [huJ]
      infer_instance
    erw [IsIso.inv_eq_inv.mpr huI, IsIso.inv_eq_inv.mpr huJ]
    change _ ≫ _ ≫ F'.rightDerivedFunctorPlus.map
      ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app G) ≫
      F'.rightDerivedFunctorPlus.map a'.hom ≫
      CategoryTheory.inv (F'.rightDerivedFunctorPlusUnith.app KJ) =
      F.rightDerivedFunctorPlus.map a.hom ≫
      CategoryTheory.inv (F.rightDerivedFunctorPlusUnith.app KI) ≫ _
    rw [← Functor.map_comp_assoc, ← ha, Functor.map_comp, Functor.map_comp,
      Category.assoc, Category.assoc]
    erw [← reassoc_of% hn, ← reassoc_of% hi]
    apply (cancel_epi (F.rightDerivedFunctorPlus.map a.hom)).2
    apply (cancel_epi (F.rightDerivedFunctorPlusUnith.app KI)).1
    simp only [IsIso.hom_inv_id_assoc]
    erw [reassoc_of% hu]
    erw [← F'.rightDerivedFunctorPlus.map_comp_assoc
      (L.mapDerivedCategoryPlusFactorsh.inv.app KI)
      (L.mapDerivedCategoryPlusFactorsh.hom.app KI), Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    erw [← reassoc_of% hf]
    erw [IsIso.hom_inv_id, Category.comp_id]
    apply DerivedCategory.Plus.ι.map_injective
    change DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex η (.up ℤ)).app I.obj) ≫
      DerivedCategory.Q.map ((F'.mapHomologicalComplex (.up ℤ)).map φ) =
      DerivedCategory.Q.map b.hom
    rw [← Functor.map_comp]
    rfl
  rw [Functor.rightDerivedBaseChange_app]
  simp only [Functor.id_map]
  rw [Functor.identityDerivedHomologyComparison]
  simp only [Functor.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso,
    NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app,
    Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hh := congrArg H.map hrep
  simp only [Functor.map_comp] at hh
  erw [reassoc_of% hh]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality]
  simp only [Iso.inv_hom_id_assoc]
  rfl

end CategoryTheory.Functor

namespace AlgebraicGeometry
open Scheme Etale

/-- Classical derived base change is computed by the section map on resolutions.
Source: Stacks Project, Tag 01F8, equation 01F9; site version Tag 08J6.
(blueprint: lem-weil-pbc-classical-pullback-resolution-sections)

Proof: Use the chosen bounded below injective resolutions I of G and J of L G.
The homotopy hφ says that φ represents the identity of L G in the derived category,
because exact inverse image carries the augmentation of I to a quasi-isomorphism.
The derived base-change transformation is characterized by compatibility with the
derived-functor units. On I this compatibility identifies it with η on each term,
followed by the derived Γ' unit on L I. Naturality of that unit along φ, and its
invertibility on J, identifies this composite with Γ'(φ) following η(I).
Apply degree-q homology and the canonical comparisons computing classical right
derived functors by the chosen resolutions. These are precisely
isoRightDerivedObjCochainComplex, so the displayed equality follows. A different
lift gives the same homology map, since additive Γ' preserves homotopies.
No acyclicity of L I for Γ' is assumed. The unit on J supplies the replacement,
so the argument applies in degree zero, to zero sheaves, and to empty schemes. -/
theorem classicalPullback_resolution_sections
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (φ : ((upperStar AddCommGrpCat.{u + 1} g').mapHomologicalComplex (.up ℤ)).obj
      (injectiveResolution G).cochainComplex ⟶
      (injectiveResolution ((upperStar AddCommGrpCat.{u + 1} g').obj G)).cochainComplex)
    (hφ : Nonempty (Homotopy
      (((upperStar AddCommGrpCat.{u + 1} g').mapHomologicalComplex (.up ℤ)).map
        (injectiveResolution G).ι' ≫ φ)
      ((HomologicalComplex.singleMapHomologicalComplex
        (upperStar AddCommGrpCat.{u + 1} g') (.up ℤ) 0).hom.app G ≫
        (injectiveResolution ((upperStar AddCommGrpCat.{u + 1} g').obj G)).ι'))) :
    let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
    let Γ' := Sheaf.Γ X'.smallEtaleTopology AddCommGrpCat.{u + 1}
    let L := upperStar AddCommGrpCat.{u + 1} g'
    let η : Γ ⟶ L ⋙ Γ' :=
      (Functor.leftUnitor Γ).inv ≫
        Functor.whiskerRight (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g').unit Γ ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft L (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} g').hom
    let b := (NatTrans.mapHomologicalComplex η (.up ℤ)).app
      (injectiveResolution G).cochainComplex ≫
        (Γ'.mapHomologicalComplex (.up ℤ)).map φ
    let e : Γ ⋙ 𝟭 _ ⟶ L ⋙ Γ' := (Functor.rightUnitor Γ).hom ≫ η
    ((injectiveResolution G).isoRightDerivedObjCochainComplex Γ q).hom ≫
        HomologicalComplex.homologyMap b (q : ℤ) =
      (Functor.rightDerivedBaseChange e q).app G ≫
        ((injectiveResolution (L.obj G)).isoRightDerivedObjCochainComplex Γ' q).hom := by
  exact Functor.resolution_baseChange_sections _ _ _ _ G q φ hφ

end AlgebraicGeometry
