/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.RightDerivedSingleUnitHomologyComparison
import all Mathlib.Algebra.Homology.Localization

/-!
# The derived unit equation for base change on single complexes

Source: `rightDerivedFunctorPlusBaseChange_fac` in
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange`
(blueprint: lem-sbc-right-derived-base-change-single-unit).
-/

@[expose] public section

namespace CategoryTheory.Functor

open Limits

variable {B B' C C' : Type*} [Category* B] [Category* B'] [Category* C] [Category* C']
  [Abelian B] [Abelian B'] [Abelian C] [Abelian C']
  [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory C] [HasDerivedCategory C']
  [EnoughInjectives B] [EnoughInjectives B']
  {G : B ⥤ C} {G' : B' ⥤ C'} {β : B ⥤ B'} {γ : C ⥤ C'}
  [G.Additive] [G'.Additive] [β.Additive] [γ.Additive]
  [PreservesFiniteLimits β] [PreservesFiniteColimits β]
  [PreservesFiniteLimits γ] [PreservesFiniteColimits γ]

private noncomputable def singleTransport (D : Type*) [Category* D] [Abelian D]
    [HasDerivedCategory D] (X : D) :
    DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor D 0).obj X) ≅
      (DerivedCategory.Plus.singleFunctor D 0).obj X :=
  (DerivedCategory.Plus.ι.preimageIso
    (X := (DerivedCategory.Plus.singleFunctor D 0).obj X)
    (Y := DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor D 0).obj X))
    ((DerivedCategory.singleFunctorIsoCompQ D 0).app X ≪≫
      (DerivedCategory.quotientCompQhIso D).symm.app _)).symm

private noncomputable def homotopySingleIso {D E : Type*} [Category* D] [Category* E]
    [Abelian D] [Abelian E] (F : D ⥤ E) [F.Additive] (X : D) :
    F.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.singleFunctor D 0).obj X) ≅
      (HomotopyCategory.Plus.singleFunctor E 0).obj (F.obj X) :=
  (HomotopyCategory.Plus.ι E).preimageIso
    ((HomotopyCategory.quotient E (.up ℤ)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app X))

private theorem singleTransport_hom (D : Type*) [Category* D] [Abelian D]
    [HasDerivedCategory D] (X : D) :
    (singleTransport D X).hom = 𝟙 _ := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [singleTransport, Iso.symm_hom, Functor.preimageIso_inv,
    Functor.map_preimage, Iso.trans_inv]
  change (DerivedCategory.quotientCompQhIso D).hom.app _ ≫ 𝟙 _ = 𝟙 _
  rw [Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem single_exact_transport {D E : Type*} [Category* D] [Category* E]
    [Abelian D] [Abelian E] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : D ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (X : D) :
    F.mapDerivedCategoryPlus.map (singleTransport D X).hom ≫
      (F.mapDerivedCategoryPlusSingleFunctor 0).hom.app X =
    F.mapDerivedCategoryPlusFactorsh.hom.app
      ((HomotopyCategory.Plus.singleFunctor D 0).obj X) ≫
      DerivedCategory.Plus.Qh.map (homotopySingleIso F X).hom ≫
      (singleTransport E (F.obj X)).hom := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp, singleTransport_hom, Functor.map_id,
    Category.id_comp, Category.comp_id,
    ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app,
    ι_map_mapDerivedCategoryPlusFactorsh_hom_app]
  change (F.mapDerivedCategorySingleFunctor 0).hom.app X =
    F.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient D (.up ℤ)).obj
        ((CochainComplex.singleFunctor D 0).obj X)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι E).map
        (homotopySingleIso F X).hom)
  rw [mapDerivedCategoryFactorsh_hom_app]
  simp only [homotopySingleIso, Functor.preimageIso_hom, Functor.map_preimage,
    Functor.mapIso_hom, Category.assoc]
  change _ = F.mapDerivedCategory.map (𝟙 _) ≫
    F.mapDerivedCategoryFactors.hom.app _ ≫ 𝟙 _ ≫
    DerivedCategory.Qh.map (𝟙 _) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient E (.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app X))
  simp only [Functor.map_id, Category.id_comp]
  erw [Category.id_comp]
  change _ = F.mapDerivedCategoryFactors.hom.app _ ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app X)
  simp only [comp_obj, DerivedCategory.Q_obj_single_obj, mapDerivedCategorySingleFunctor,
    DerivedCategory.singleFunctorIsoCompQ, isoWhiskerRight_refl, isoWhiskerLeft_refl,
    Iso.refl_symm, Iso.refl_trans, Iso.trans_hom, isoWhiskerLeft_hom, Iso.symm_hom,
    isoWhiskerRight_hom, Iso.refl_hom, NatTrans.comp_app, associator_hom_app,
    whiskerLeft_app, associator_inv_app, whiskerRight_app, NatTrans.id_app,
    Category.comp_id, Category.id_comp]
  erw [Category.id_comp]

private theorem single_comparison {D E : Type*} [Category* D] [Category* E]
    [Abelian D] [Abelian E] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : D ⥤ E) [F.Additive] (X : D) :
    DerivedCategory.Plus.Qh.map (homotopySingleIso F X).hom =
      (F.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 X).hom := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [mapHomotopyCategoryPlusSingleFunctorQhObjIso, Functor.preimageIso_hom,
    Functor.map_preimage]
  change DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι E).map
    (homotopySingleIso F X).hom) = _
  simp only [homotopySingleIso, Functor.preimageIso_hom, Functor.map_preimage,
    Functor.mapIso_hom]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom]
  erw [Category.id_comp]
  rfl

omit [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory C]
  [EnoughInjectives B] [EnoughInjectives B'] [PreservesFiniteLimits β]
  [PreservesFiniteColimits β] [PreservesFiniteLimits γ] [PreservesFiniteColimits γ] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem single_naturality (e : G ⋙ γ ⟶ β ⋙ G') (Y : B) :
    DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e).app
        ((HomotopyCategory.Plus.singleFunctor B 0).obj Y)) ≫
      DerivedCategory.Plus.Qh.map
        (G'.mapHomotopyCategoryPlus.map (homotopySingleIso β Y).hom) ≫
      (G'.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 (β.obj Y)).hom =
    DerivedCategory.Plus.Qh.map
        (γ.mapHomotopyCategoryPlus.map (homotopySingleIso G Y).hom) ≫
      (γ.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 (G.obj Y)).hom ≫
      (DerivedCategory.Plus.singleFunctor C' 0).map (e.app Y) := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp, mapHomotopyCategoryPlusSingleFunctorQhObjIso,
    Functor.preimageIso_hom, Functor.map_preimage]
  simp only [Iso.trans_hom, Iso.app_hom, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom]
  erw [Category.id_comp, Category.id_comp]
  change DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι C').map
      ((NatTrans.mapHomotopyCategoryPlus e).app
        ((HomotopyCategory.Plus.singleFunctor B 0).obj Y))) ≫
      DerivedCategory.Qh.map (G'.mapHomotopyCategory (.up ℤ) |>.map
        ((HomotopyCategory.Plus.ι B').map (homotopySingleIso β Y).hom)) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex G' (.up ℤ) 0).hom.app
          (β.obj Y)) =
    DerivedCategory.Qh.map (γ.mapHomotopyCategory (.up ℤ) |>.map
      ((HomotopyCategory.Plus.ι C).map (homotopySingleIso G Y).hom)) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex γ (.up ℤ) 0).hom.app
          (G.obj Y)) ≫
      (DerivedCategory.singleFunctor C' 0).map (e.app Y)
  rw [NatTrans.ι_map_mapHomotopyCategoryPlus_app]
  simp only [homotopySingleIso, Functor.preimageIso_hom, Functor.map_preimage,
    Functor.mapIso_hom, Functor.mapHomotopyCategory_map, NatTrans.mapHomotopyCategory_app]
  change DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex e (.up ℤ)).app
        ((CochainComplex.singleFunctor B 0).obj Y)) ≫
      DerivedCategory.Q.map ((G'.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex β (.up ℤ) 0).hom.app Y)) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex G' (.up ℤ) 0).hom.app
          (β.obj Y)) =
    DerivedCategory.Q.map ((γ.mapHomologicalComplex (.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app Y)) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex γ (.up ℤ) 0).hom.app
          (G.obj Y)) ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor C' 0).map (e.app Y))
  simp only [← Functor.map_comp]
  congr 1
  ext n
  by_cases hn : n = 0
  · subst n
    simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      CochainComplex.singleFunctor,
      HomologicalComplex.single_map_f_self]
    dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
    simp only [Functor.map_id, Category.id_comp]
    change e.app Y ≫ G'.map (𝟙 (β.obj Y)) ≫ 𝟙 _ =
      γ.map (𝟙 (G.obj Y)) ≫ 𝟙 _ ≫ e.app Y ≫ 𝟙 _
    simp only [Functor.map_id, Category.id_comp, Category.comp_id]
    exact Category.comp_id _
  · have hz := HomologicalComplex.singleMapHomologicalComplex_hom_app_ne
      G' (.up ℤ) hn (β.obj Y)
    have hz' := HomologicalComplex.singleMapHomologicalComplex_hom_app_ne
      γ (.up ℤ) hn (G.obj Y)
    simp only [HomologicalComplex.comp_f, hz, hz', comp_zero,
      zero_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The derived base-change equation on single complexes, before taking homology.

Source: `rightDerivedFunctorPlusBaseChange_fac` in `PlusBaseChange.lean`.
(blueprint: lem-sbc-right-derived-base-change-single-unit).

Proof: evaluate the defining base-change unit equation on the homotopy single
complex Y[0]. Expand the auxiliary transformation. The composition comparisons
identify the transformation induced by e with the single-complex map of e(Y).
Transport the source and target along the canonical isomorphisms from Qh of
homotopy single complexes to derived single complexes. Naturality of the derived
base-change transformation moves this transport to its target; naturality of the
unit for G' identifies the resulting map with its unit on beta(Y)[0]. The exact
functor comparisons for gamma and beta supply the displayed single-complex
comparison maps. This yields the equation without any left-exactness assumption
on G or G'. -/
theorem rightDerivedBaseChange_single_unit (e : G ⋙ γ ⟶ β ⋙ G') (Y : B) :
    γ.mapDerivedCategoryPlus.map (G.rightDerivedPlusSingleUnit Y) ≫
      (rightDerivedFunctorPlusBaseChange e).app
        ((DerivedCategory.Plus.singleFunctor B 0).obj Y) ≫
      G'.rightDerivedFunctorPlus.map
        ((β.mapDerivedCategoryPlusSingleFunctor 0).hom.app Y) =
    (γ.mapDerivedCategoryPlusSingleFunctor 0).hom.app (G.obj Y) ≫
      (DerivedCategory.Plus.singleFunctor C' 0).map (e.app Y) ≫
      G'.rightDerivedPlusSingleUnit (β.obj Y) := by
  let K := (HomotopyCategory.Plus.singleFunctor B 0).obj Y
  have hfac := congr_app (rightDerivedFunctorPlusBaseChange_fac e) K
  simp only [NatTrans.comp_app, whiskerRight_app, Functor.associator_hom_app,
    Category.comp_id, whiskerLeft_app] at hfac
  have ht := single_exact_transport β Y
  simp only [singleTransport_hom, Functor.map_id, Category.id_comp,
    Category.comp_id] at ht
  have hu := G'.rightDerivedFunctorPlusUnith.naturality (homotopySingleIso β Y).hom
  dsimp only [Functor.comp_map] at hu
  change γ.mapDerivedCategoryPlus.map
      ((G.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 Y).inv ≫
        G.rightDerivedFunctorPlusUnith.app K ≫ G.rightDerivedFunctorPlus.map
          (singleTransport B Y).hom) ≫ _ =
    _ ≫ _ ≫ (G'.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 (β.obj Y)).inv ≫
      G'.rightDerivedFunctorPlusUnith.app _ ≫ G'.rightDerivedFunctorPlus.map
        (singleTransport B' (β.obj Y)).hom
  rw [singleTransport_hom, singleTransport_hom]
  erw [Functor.map_id, Functor.map_id]
  erw [Category.comp_id, Category.comp_id]
  rw [Functor.map_comp, Category.assoc]
  erw [← Category.assoc (γ.mapDerivedCategoryPlus.map
    (G.rightDerivedFunctorPlusUnith.app K)), hfac]
  simp only [rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
    whiskerRight_app, whiskerLeft_app, Functor.associator_inv_app,
    Functor.associator_hom_app, mapHomotopyCategoryPlusCompIso_refl_hom_app,
    mapHomotopyCategoryPlusCompIso_refl_inv_app, Functor.map_id,
    Category.id_comp, Category.comp_id, Category.assoc]
  rw [ht, Functor.map_comp]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
  rw [← hu]
  erw [Category.id_comp, Category.id_comp]
  have hn := single_naturality e Y
  have hn' : DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e).app K) ≫
      DerivedCategory.Plus.Qh.map
        (G'.mapHomotopyCategoryPlus.map (homotopySingleIso β Y).hom) =
    DerivedCategory.Plus.Qh.map
        (γ.mapHomotopyCategoryPlus.map (homotopySingleIso G Y).hom) ≫
      (γ.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 (G.obj Y)).hom ≫
      (DerivedCategory.Plus.singleFunctor C' 0).map (e.app Y) ≫
      (G'.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 (β.obj Y)).inv := by
    apply (cancel_mono
      (G'.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 (β.obj Y)).hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hn
  rw [reassoc_of% hn']
  have hg := γ.mapDerivedCategoryPlusFactorsh.hom.naturality (homotopySingleIso G Y).hom
  dsimp only [Functor.comp_map] at hg
  rw [← reassoc_of% hg, single_comparison, ← Functor.map_comp_assoc,
    Iso.inv_hom_id, Functor.map_id, Category.id_comp]
  have hγ := single_exact_transport γ (G.obj Y)
  simp only [singleTransport_hom, Functor.map_id, Category.id_comp,
    Category.comp_id, single_comparison] at hγ
  rw [← reassoc_of% hγ]

end CategoryTheory.Functor
