/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus
import all Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
/-!
# The derived unit and the classical degree-zero augmentation

Source: Stacks Project, Derived Categories, Tag 05TD, part (3), and the unit
characterization of derived base change
(blueprint: lem-sbc-right-derived-single-unit-homology-comparison).
-/

@[expose] public section

namespace CategoryTheory.Functor

variable {B C : Type*} [Category* B] [Category* C] [Abelian B] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory C] [EnoughInjectives B]
  (G : B ⥤ C) [G.Additive]

/-- The unit on an object placed in degree zero, using the single-complex comparisons.

Source: `rightDerivedFunctorPlusUnith` and `mapHomotopyCategoryPlusSingleFunctorQhObjIso`
in `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`.
(blueprint: lem-sbc-right-derived-single-unit-homology-comparison). -/
noncomputable def rightDerivedPlusSingleUnit (Y : B) :
    (DerivedCategory.Plus.singleFunctor C 0).obj (G.obj Y) ⟶
      G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj Y) :=
  (G.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 Y).inv ≫
    G.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor B 0).obj Y) ≫
    G.rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.ι.preimageIso
        (X := (DerivedCategory.Plus.singleFunctor B 0).obj Y)
        (Y := DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor B 0).obj Y))
        ((DerivedCategory.singleFunctorIsoCompQ B 0).app Y ≪≫
          (DerivedCategory.quotientCompQhIso B).symm.app _)).inv

/-- Degree-zero homology of the derived unit on a single complex.

Source: the preceding unit and `DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso`
in `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus`.
(blueprint: lem-sbc-right-derived-single-unit-homology-comparison). -/
noncomputable def rightDerivedPlusSingleUnitHomology (Y : B) :
    G.obj Y ⟶ (DerivedCategory.Plus.homologyFunctor C 0).obj
      (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj Y)) :=
  (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app (G.obj Y) ≫
    (DerivedCategory.Plus.homologyFunctor C 0).map (G.rightDerivedPlusSingleUnit Y)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The single-complex homology comparison identifies the derived unit with the
classical augmentation.

Source: Stacks Project, Derived Categories, Tag 05TD, part (3), and the definitions of
`homologyRightDerivedFunctorPlusObjSingleFunctorIso` and `toRightDerivedZero`.
(blueprint: lem-sbc-right-derived-single-unit-homology-comparison).

Proof: choose the injective resolution of Y used in both definitions. Naturality of the
right-derived unit along the resolution augmentation identifies the unit on Y[0] with
its map into the resolution followed by the unit on that resolution. The latter unit
is invertible, and cancels with its inverse in the definition of the single-complex
comparison. Apply homologyFunctorObjQIso naturality to the remaining resolution map.
The embedding from natural-number complexes to integer complexes preserves degree-zero
homology. Under this identification the remaining map is the lift of G applied to the
resolution augmentation into degree-zero cycles, followed by isoHomologyπ₀. This is
exactly InjectiveResolution.toRightDerivedZero', and composing isoRightDerivedObj.inv
gives G.toRightDerivedZero.app Y. -/
theorem rightDerivedPlusSingleUnitHomology_comp_comparison (Y : B) :
    G.rightDerivedPlusSingleUnitHomology Y ≫
      (G.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0).hom.app Y =
    G.toRightDerivedZero.app Y := by
  -- Cancel the unit on the resolution using naturality along its augmentation.
  let R := injectiveResolution Y
  let S : CochainComplex.Plus B :=
    ⟨(CochainComplex.singleFunctor B 0).obj Y, 0, inferInstance⟩
  let L : CochainComplex.Plus B := ⟨R.cochainComplex, 0, inferInstance⟩
  let g : S ⟶ L := ObjectProperty.homMk R.ι'
  let SC : CochainComplex.Plus C :=
    ⟨(CochainComplex.singleFunctor C 0).obj (G.obj Y), 0, inferInstance⟩
  let s : SC ⟶ G.mapCochainComplexPlus.obj S := ObjectProperty.homMk
    ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).inv.app Y)
  let a := (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).inv.app Y ≫
    (G.mapHomologicalComplex (.up ℤ)).map R.ι'
  let a' : SC ⟶ G.rightDerivedPlusComplex Y := ObjectProperty.homMk a
  have hsource : (G.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 Y).inv =
      DerivedCategory.Plus.Q.map s ≫
        (DerivedCategory.Plus.quotientCompQhIso C).inv.app
          (G.mapCochainComplexPlus.obj S) := by
    apply DerivedCategory.Plus.ι.map_injective
    simp only [ObjectProperty.ι_obj, mapHomotopyCategoryPlusSingleFunctorQhObjIso, preimageIso_inv,
      Iso.trans_inv, mapIso_inv, Iso.app_inv, NatTrans.naturality, DerivedCategory.Q_obj_single_obj,
      comp_obj, comp_map, ObjectProperty.ι_map, DerivedCategory.Plus.quotientCompQhIso,
      NatIso.ofComponents_inv_app, mapCochainComplexPlus_obj_obj, ObjectProperty.isoMk_inv,
      ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, SC, S, s]
    change DerivedCategory.Plus.ι.map (DerivedCategory.Plus.ι.preimage _) = _
    rw [Functor.map_preimage]
    exact ((DerivedCategory.quotientCompQhIso C).inv.naturality _).symm
  have htarget :
      (DerivedCategory.Plus.ι.preimageIso
        (X := (DerivedCategory.Plus.singleFunctor B 0).obj Y)
        (Y := DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor B 0).obj Y))
        ((DerivedCategory.singleFunctorIsoCompQ B 0).app Y ≪≫
          (DerivedCategory.quotientCompQhIso B).symm.app _)).inv =
      (DerivedCategory.Plus.quotientCompQhIso B).hom.app S := by
    apply DerivedCategory.Plus.ι.map_injective
    simp only [ObjectProperty.ι_obj, comp_obj, DerivedCategory.singleFunctorIsoCompQ,
      preimageIso_inv, Iso.trans_inv, Iso.app_inv, Iso.symm_inv, Iso.refl_inv, NatTrans.id_app,
      ObjectProperty.ι_map, DerivedCategory.Plus.quotientCompQhIso, NatIso.ofComponents_hom_app,
      ObjectProperty.isoMk_hom, Iso.app_hom, ObjectProperty.homMk_hom, S]
    change DerivedCategory.Plus.ι.map (DerivedCategory.Plus.ι.preimage _) = _
    rw [Functor.map_preimage]
    exact Category.comp_id _
  have hsingleUnit : G.rightDerivedPlusSingleUnit Y =
      DerivedCategory.Plus.Q.map s ≫ G.rightDerivedFunctorPlusUnit.app S := by
    simp only [rightDerivedPlusSingleUnit, hsource, htarget]
    simp only [comp_obj, NatTrans.naturality, comp_map, Category.assoc, rightDerivedFunctorPlusUnit,
      quotientCompMapHomotopyCategoryPlusIso, Iso.refl_inv, NatTrans.comp_app, whiskerLeft_app,
      associator_inv_app, whiskerRight_app, NatTrans.id_app, associator_hom_app, Category.id_comp,
      NatTrans.naturality_assoc, NatIso.cancel_natIso_inv_left]
    erw [Functor.map_id]
    simp
    rfl
  have : ∀ n, Injective (L.obj.X n) := fun n ↦
    inferInstanceAs (Injective (R.cochainComplex.X n))
  have : IsIso (G.rightDerivedFunctorPlusUnit.app L) := by
    let L' : CochainComplex (InjectiveObject B) ℤ :=
      HomologicalComplex.liftObjectProperty _ R.cochainComplex inferInstance
    have hL' : L'.IsStrictlyGE 0 := by
      rw [← CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ (InjectiveObject.ι B)]
      exact inferInstanceAs (R.cochainComplex.IsStrictlyGE 0)
    exact inferInstanceAs (IsIso (G.rightDerivedFunctorPlusUnit.app
      ((InjectiveObject.ι B).mapCochainComplexPlus.obj ⟨L', 0, hL'⟩)))
  have hresolution : (G.rightDerivedFunctorPlusObjSingleFunctorIsoQ Y).hom =
      G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map g) ≫
        CategoryTheory.inv (G.rightDerivedFunctorPlusUnit.app L) := by
    simp only [rightDerivedFunctorPlusObjSingleFunctorIsoQ, ObjectProperty.ι_obj, comp_obj,
      DerivedCategory.singleFunctorIsoCompQ, Iso.trans_hom, mapIso_hom, preimageIso_hom,
      Iso.app_hom, Iso.refl_hom, NatTrans.id_app, asIso_hom, Iso.symm_hom, asIso_inv,
      IsIso.eq_comp_inv, Category.assoc, IsIso.inv_hom_id, Category.comp_id, L, R, g]
    congr 1
    apply DerivedCategory.Plus.ι.map_injective
    rw [Functor.map_preimage]
    exact Category.id_comp _
  have hcancel : G.rightDerivedPlusSingleUnit Y ≫
      (G.rightDerivedFunctorPlusObjSingleFunctorIsoQ Y).hom =
      DerivedCategory.Plus.Q.map a' := by
    rw [hsingleUnit, hresolution, Category.assoc]
    have hunit := G.rightDerivedFunctorPlusUnit.naturality g
    dsimp only [Functor.comp_map] at hunit
    rw [← Category.assoc _ _ (CategoryTheory.inv _), ← hunit, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id, ← Functor.map_comp]
    rfl
  simp only [rightDerivedPlusSingleUnitHomology,
    singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso,
    NatIso.ofComponents_hom_app, homologyRightDerivedFunctorPlusObjSingleFunctorIso,
    Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  erw [← Functor.map_comp_assoc, hcancel]
  erw [DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality_assoc]
  -- Remove the single-complex and quotient homology comparisons.
  have hsingle :
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app (G.obj Y) ≫
        (DerivedCategory.Plus.homologyFunctorObjQIso SC 0).hom =
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (G.obj Y)).inv := by
    simp [DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso,
      DerivedCategory.singleFunctorCompHomologyFunctorIso,
      DerivedCategory.singleFunctorsPostcompQIso, HomologicalComplex.homologyFunctorSingleIso,
      DerivedCategory.Plus.homologyFunctorObjQIso, SC]
  erw [← Category.assoc, hsingle]
  rw [R.toRightDerivedZero_eq G]
  simp only [InjectiveResolution.isoRightDerivedObjCochainComplex,
    Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    HomologicalComplex.homologyFunctor_map, Category.assoc]
  simp only [← Category.assoc]
  apply (cancel_mono (R.isoRightDerivedObj G 0).inv).2
  let K := (G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex
  let b := a ≫ (R.cocomplex.mapExtendIso ComplexShape.embeddingUpNat G).hom
  -- Identify the degree-zero cycles lift by composing with the cycles inclusion.
  have hc :
      (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 (G.obj Y)).inv ≫
        HomologicalComplex.cyclesMap b 0 ≫
        (K.extendCyclesIso ComplexShape.embeddingUpNat (by simp : (0 : ℕ) = (0 : ℤ))).hom =
      R.toRightDerivedZero' G := by
    apply (cancel_mono (K.iCycles 0)).1
    simp only [Category.assoc, HomologicalComplex.extendCyclesIso_hom_iCycles]
    erw [HomologicalComplex.cyclesMap_i_assoc,
      InjectiveResolution.toRightDerivedZero'_comp_iCycles]
    erw [HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles_assoc]
    dsimp [b, a]
    simp only [HomologicalComplex.singleMapHomologicalComplex_inv_app_self, Category.assoc]
    rw [InjectiveResolution.ι'_f_zero]
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]
    simp only [Iso.inv_hom_id_assoc]
    dsimp [InjectiveResolution.cochainComplexXIso, HomologicalComplex.mapExtendIso,
      HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso]
    erw [HomologicalComplex.mapExtendX_hom_eq R.cocomplex G
      (ComplexShape.embeddingUpNat.r_f 0)]
    simp [eqToHom_map]
  simp only [Category.assoc]
  erw [← HomologicalComplex.homologyMap_comp_assoc]
  change (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (G.obj Y)).inv ≫
    HomologicalComplex.homologyMap b 0 ≫
      (K.extendHomologyIso ComplexShape.embeddingUpNat (by simp : (0 : ℕ) = (0 : ℤ))).hom = _
  rw [← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ,
    Category.assoc, HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_extendHomologyIso_hom]
  change _ = R.toRightDerivedZero' G ≫ K.homologyπ 0
  exact (by simpa only [Category.assoc] using
    congrArg (fun f => f ≫ K.homologyπ 0) hc)

end CategoryTheory.Functor
