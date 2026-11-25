/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Exact pullback and resolution augmentations

Source: Stacks Project, Tags 01F8 and 05TH.
(blueprint: lem-weil-pbc-resolution-pullback-augmentation).
-/

@[expose] public section

open CategoryTheory Limits Category
namespace CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An exact functor carries the resolution augmentation square to its derived image.
Source: Stacks Project, Tag 01F8 (cohomology.tex, lemma-functoriality), and
Tag 05TH (derived.tex, lemma-injective-acyclic).
(blueprint: lem-weil-pbc-resolution-pullback-augmentation).

Proof: Apply the fully faithful inclusion from D+ to D. Its image of a and a'
is the single-complex comparison followed by Q of the respective augmentation
and the inverse quotient/Qh comparison. The image of the exact-functor
factorization is mapDerivedCategoryFactorsh on the resolution. Expand it into
the Q factorization and cancel the adjacent quotient/Qh comparisons.
Naturality of mapDerivedCategoryFactors along the augmentation moves L past
that augmentation. Expand mapDerivedCategorySingleFunctor; its final inverse
single-complex comparison cancels the first comparison in a'. Both sides now
have the same initial single-complex comparison and exact-functor factorization.
The remaining equality is Q(L(ι') ≫ φ) = Q(singleMap.hom ≫ ι'). It follows from
the supplied homotopy, since Q identifies homotopic maps. Faithfulness gives
the original equality. No preservation of injective objects is used; no separate
quasi-isomorphism hypothesis on φ is needed. Zero objects and zero complexes
satisfy the same calculation. -/
theorem resolution_pullback_augmentation
    {A A' : Type*} [Category* A] [Category* A'] [Abelian A] [Abelian A']
    [HasDerivedCategory A] [HasDerivedCategory A']
    [EnoughInjectives A] [EnoughInjectives A']
    (L : A ⥤ A') [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] (Y : A)
    (φ : (L.mapHomologicalComplex (.up ℤ)).obj
      (injectiveResolution Y).cochainComplex ⟶
      (injectiveResolution (L.obj Y)).cochainComplex)
    (hφ : Nonempty (Homotopy
      ((L.mapHomologicalComplex (.up ℤ)).map (injectiveResolution Y).ι' ≫ φ)
      ((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).hom.app Y ≫
        (injectiveResolution (L.obj Y)).ι'))) :
    let I : CochainComplex.Plus A :=
      ⟨(injectiveResolution Y).cochainComplex, 0, inferInstance⟩
    let J : CochainComplex.Plus A' :=
      ⟨(injectiveResolution (L.obj Y)).cochainComplex, 0, inferInstance⟩
    let LI : CochainComplex.Plus A' :=
      ⟨(L.mapHomologicalComplex (.up ℤ)).obj I.obj, 0, inferInstance⟩
    let a := DerivedCategory.Plus.ι.preimageIso
      (X := (DerivedCategory.Plus.singleFunctor A 0).obj Y)
      (Y := (HomotopyCategory.Plus.quotient A ⋙ DerivedCategory.Plus.Qh).obj I)
      ((DerivedCategory.singleFunctorIsoCompQ A 0).app Y ≪≫
        asIso (DerivedCategory.Q.map (injectiveResolution Y).ι') ≪≫
        (DerivedCategory.quotientCompQhIso A).symm.app _)
    let a' := DerivedCategory.Plus.ι.preimageIso
      (X := (DerivedCategory.Plus.singleFunctor A' 0).obj (L.obj Y))
      (Y := (HomotopyCategory.Plus.quotient A' ⋙ DerivedCategory.Plus.Qh).obj J)
      ((DerivedCategory.singleFunctorIsoCompQ A' 0).app (L.obj Y) ≪≫
        asIso (DerivedCategory.Q.map (injectiveResolution (L.obj Y)).ι') ≪≫
        (DerivedCategory.quotientCompQhIso A').symm.app _)
    L.mapDerivedCategoryPlus.map a.hom ≫
        L.mapDerivedCategoryPlusFactorsh.hom.app ((HomotopyCategory.Plus.quotient A).obj I) ≫
        (HomotopyCategory.Plus.quotient A' ⋙ DerivedCategory.Plus.Qh).map
          (ObjectProperty.homMk φ : LI ⟶ J) =
      (L.mapDerivedCategoryPlusSingleFunctor 0).hom.app Y ≫ a'.hom := by
  dsimp only
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp,
    ι_map_mapDerivedCategoryPlusFactorsh_hom_app,
    ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app,
    Functor.preimageIso_hom, Functor.map_preimage, Iso.trans_hom, asIso_hom]
  simp only [mapDerivedCategoryPlus, ObjectProperty.lift_map,
    ObjectProperty.ι_map, Functor.comp_map]
  change L.mapDerivedCategory.map (DerivedCategory.Plus.ι.map
    (DerivedCategory.Plus.ι.preimage _)) ≫ _ ≫ _ = _
  rw [Functor.map_preimage]
  erw [L.mapDerivedCategoryFactorsh_hom_app (injectiveResolution Y).cochainComplex]
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [Iso.app, Iso.symm_hom, Iso.symm_inv]
  erw [← L.mapDerivedCategory.map_comp_assoc
    ((DerivedCategory.quotientCompQhIso A).inv.app _)
    ((DerivedCategory.quotientCompQhIso A).hom.app _), Iso.inv_hom_id_app]
  have hi : (L.mapHomotopyCategoryFactors (.up ℤ)).inv.app
      (injectiveResolution Y).cochainComplex = 𝟙 _ := rfl
  rw [hi]
  simp only [Functor.map_id, Category.id_comp]
  erw [DerivedCategory.Qh.map_id, Category.id_comp]
  change _ ≫ _ ≫ _ ≫ (DerivedCategory.quotientCompQhIso A').inv.app _ ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient A' (.up ℤ)).map φ) = _
  erw [← DerivedCategory.quotientCompQhIso_inv_naturality]
  simp only [mapDerivedCategorySingleFunctor, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    isoWhiskerLeft_inv, whiskerRight_app, whiskerLeft_app,
    associator_hom_app, associator_inv_app, Category.id_comp,
    Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  have hn := L.mapDerivedCategoryFactors.hom.naturality (injectiveResolution Y).ι'
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  obtain ⟨h⟩ := hφ
  rw [DerivedCategory.Q_map_eq_of_homotopy A' h]

end CategoryTheory.Functor
