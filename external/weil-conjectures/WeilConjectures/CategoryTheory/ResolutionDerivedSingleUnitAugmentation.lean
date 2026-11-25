/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
public import WeilConjectures.CategoryTheory.CanonicalResolutionDerivedIso
public import WeilConjectures.CategoryTheory.RightDerivedSingleUnitHomologyComparison

/-! # The derived unit and an augmented resolution comparison

Source: Stacks Project, Derived Categories, Tag 015M.
(blueprint: lem-sc-resolution-derived-single-unit-augmentation)
-/

@[expose] public section

universe uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- The derived unit, transported to a prescribed resolution, is the augmented comparison.
Source: Stacks Project, Derived Categories, Tag 015M, resolution computation and naturality.
(blueprint: lem-sc-resolution-derived-single-unit-augmentation).

Proof: Naturality of the derived unit along the augmentation of I cancels its inverse
on I in resolutionDerivedIso. The remaining map is F applied to the augmentation,
followed by the map/extension comparison. The hypothesis on phi identifies this with
the augmentation of J followed by the extension of phi: check degree zero, and use
that the source is zero in every other degree. Apply localization to this equality.
The single-complex and quotient comparisons identify its source with F(X)[0].
-/
theorem resolutionDerivedSingleUnit_augmentation
    {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive]
    (X : A) (I : InjectiveResolution X) (J : InjectiveResolution (F.obj X))
    (φ : J.cocomplex ⟶ (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
    (hφ : J.ι.f 0 ≫ φ.f 0 = F.map (I.ι.f 0)) :
    let K := (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
    let L : CochainComplex.Plus B :=
      ⟨K.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩
    let f : (⟨J.cochainComplex, 0, inferInstance⟩ : CochainComplex.Plus B) ⟶ L :=
      ObjectProperty.homMk (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)
    F.rightDerivedPlusSingleUnit X ≫ (canonicalResolutionDerivedIso F I).hom =
      (resolutionAugmentationIso J).hom ≫ DerivedCategory.Plus.Q.map f := by
  let S : CochainComplex.Plus A :=
    ⟨(CochainComplex.singleFunctor A 0).obj X, 0, inferInstance⟩
  let LI : CochainComplex.Plus A := ⟨I.cochainComplex, 0, inferInstance⟩
  let g : S ⟶ LI := ObjectProperty.homMk I.ι'
  have htransport :
      (DerivedCategory.Plus.ι.preimageIso
        (X := (DerivedCategory.Plus.singleFunctor A 0).obj X)
        (Y := DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor A 0).obj X))
        ((DerivedCategory.singleFunctorIsoCompQ A 0).app X ≪≫
          (DerivedCategory.quotientCompQhIso A).symm.app _)).inv ≫
      (resolutionAugmentationIso I).hom ≫
        (DerivedCategory.Plus.quotientCompQhIso A).inv.app LI =
      DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient A).map g) := by
    apply DerivedCategory.Plus.ι.map_injective
    simp only [resolutionAugmentationIso, Functor.map_comp, Functor.preimageIso_inv,
      Functor.preimageIso_hom, Functor.map_preimage, Iso.trans_inv, Iso.trans_hom,
      Category.assoc, Iso.inv_hom_id_assoc, asIso_hom]
    change (DerivedCategory.quotientCompQhIso A).hom.app _ ≫
      DerivedCategory.Q.map I.ι' ≫ (DerivedCategory.quotientCompQhIso A).inv.app _ = _
    erw [(DerivedCategory.quotientCompQhIso A).inv.naturality]
    simp
    rfl
  rw [← Category.assoc] at htransport
  have hunit := F.rightDerivedFunctorPlusUnith.naturality
    ((HomotopyCategory.Plus.quotient A).map g)
  have hcancel : F.rightDerivedPlusSingleUnit X ≫ (resolutionDerivedIso F I).hom =
      (F.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 X).inv ≫
        DerivedCategory.Plus.Qh.map
          (F.mapHomotopyCategoryPlus.map ((HomotopyCategory.Plus.quotient A).map g)) ≫
        (DerivedCategory.Plus.quotientCompQhIso B).hom.app
          (F.mapCochainComplexPlus.obj LI) := by
    dsimp [Functor.rightDerivedPlusSingleUnit, resolutionDerivedIso]
    rw [Category.assoc, Category.assoc, ← Functor.map_comp_assoc,
      ← Functor.map_comp_assoc, htransport]
    dsimp only [Functor.comp_map] at hunit
    erw [← reassoc_of% hunit, IsIso.hom_inv_id_assoc]
  let a := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app X ≫
    (F.mapHomologicalComplex (.up ℤ)).map I.ι' ≫
      (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F).hom
  have ha : J.ι' ≫ HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat = a := by
    apply HomologicalComplex.from_single_hom_ext
    simp only [HomologicalComplex.comp_f, InjectiveResolution.ι'_f_zero,
      HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0) (i' := 0) (by simp),
      Category.assoc]
    dsimp [a]
    simp only [
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      InjectiveResolution.ι'_f_zero, Functor.map_comp, Category.assoc]
    simp only [InjectiveResolution.cochainComplexXIso, Iso.inv_hom_id_assoc]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]
    erw [reassoc_of% hφ]
    dsimp [InjectiveResolution.cochainComplexXIso, HomologicalComplex.mapExtendIso,
      HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso]
    erw [HomologicalComplex.mapExtendX_hom_eq I.cocomplex F
      (ComplexShape.embeddingUpNat.r_f 0)]
    simp [eqToHom_map]
  simp only [canonicalResolutionDerivedIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hcancel]
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp, Functor.mapHomotopyCategoryPlusSingleFunctorQhObjIso,
    Functor.preimageIso_inv, Functor.map_preimage,
    resolutionAugmentationIso, Functor.preimageIso_hom]
  dsimp
  simp only [Category.assoc]
  change DerivedCategory.Q.map _ ≫ (DerivedCategory.quotientCompQhIso B).inv.app _ ≫
      DerivedCategory.Qh.map
        (F.mapHomotopyCategory (.up ℤ) |>.map
          ((HomotopyCategory.quotient A (.up ℤ)).map I.ι')) ≫
      (DerivedCategory.quotientCompQhIso B).hom.app _ ≫ DerivedCategory.Q.map _ = _
  rw [Functor.mapHomotopyCategory_map]
  simp only [← DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  erw [Iso.inv_hom_id_app_assoc]
  change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ =
    𝟙 _ ≫ DerivedCategory.Q.map J.ι' ≫
      DerivedCategory.Q.map (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)
  simp only [Category.id_comp, ← Functor.map_comp, ha]
  rfl

end CategoryTheory
