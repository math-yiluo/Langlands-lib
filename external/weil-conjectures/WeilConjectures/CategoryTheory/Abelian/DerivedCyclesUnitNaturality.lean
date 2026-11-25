/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

public import WeilConjectures.CategoryTheory.Abelian.DerivedCyclesMap
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.Abelian.DerivedSingleShiftNormalization

/-! # Derived-unit naturality on canonical cycles
Source: Stacks Project, Tags 05TC (2) and 05TD (3).
(blueprint: new-lem-pc-derived-cycles-unit-naturality).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uC vC uD vD wC wD
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
  [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  (S : C ⥤ D) [S.Additive] [PreservesFiniteLimits S]

omit [PreservesFiniteLimits S] in
/-- Naturality of the actual derived unit for the map from cycles in one degree.
This holds for any bounded-below target M and any q, without a truncation
or concentration hypothesis on M.
Source: Stacks Project, Tags 05TC (2) and 05TD (3).
(blueprint: new-lem-pc-derived-cycles-unit-naturality).

Proof: Use the chain map whose component in degree n is iCycles and whose
other components are zero. Naturality of the unbounded derived unit for
this chain map expresses the homology of the unit after the canonical
cycle lift as the homology of the unit on the single cycles object followed
by the derived image of cyclesDerivedMap. The mapped chain map has degree-n
component S(iCycles); the kernel lifting property and homologyπ naturality
identify its homology with the liftCycles in the formula. Compose with q.
Naturality of the bounded-below/unbounded compatibility moves its inverse
past the derived image of cyclesDerivedMap followed by q. The uniqueness
comparison defining this compatibility intertwines the actual derived
units. On the single object this is exactly rightDerivedPlusSingleUnitAt,
including its homotopy-single/localization comparison. Apply homology and
cancel the single/homology and localization/homology isomorphisms to give
the stated equation. -/
theorem rightDerived_cycles_unit_naturality (n : ℤ) (K : CochainComplex C ℤ)
    (M : DerivedCategory.Plus C) (q : DerivedCategory.Q.obj K ⟶
      DerivedCategory.Plus.ι.obj M) :
    ((((S.mapHomologicalComplex (.up ℤ)).obj K).sc n).liftCycles
        (S.map (K.sc n).iCycles) (by
          change S.map (K.sc n).iCycles ≫ S.map (K.sc n).g = 0
          rw [← S.map_comp, (K.sc n).iCycles_g, S.map_zero])) ≫
      (((S.mapHomologicalComplex (.up ℤ)).obj K).sc n).homologyπ ≫
      (DerivedCategory.homologyFunctorFactors D n).inv.app
        ((S.mapHomologicalComplex (.up ℤ)).obj K) ≫
      (DerivedCategory.homologyFunctor D n).map
        ((DerivedCategory.quotientCompQhIso D).inv.app
            ((S.mapHomologicalComplex (.up ℤ)).obj K) ≫
          S.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) ≫
          S.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C).hom.app K)) ≫
      (DerivedCategory.homologyFunctor D n).map (S.rightDerivedFunctor.map q) ≫
      (DerivedCategory.homologyFunctor D n).map
        (S.rightDerivedFunctorPlusCompatibility.inv.app M) =
    S.rightDerivedPlusSingleUnitHomologyAt n ((K.sc n).cycles) ≫
      (DerivedCategory.Plus.homologyFunctor D n).map
        (S.rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.ι.preimage
            (X := (DerivedCategory.Plus.singleFunctor C n).obj ((K.sc n).cycles))
            (Y := M) (DerivedCategory.cyclesDerivedMap n K ≫ q))) := by
  let Y := (K.sc n).cycles
  let A := (CochainComplex.singleFunctor C n).obj Y
  let J := (HomotopyCategory.Plus.singleFunctor C n).obj Y
  have hcunit : S.rightDerivedFunctorUnit.app ((HomotopyCategory.Plus.ι C).obj J) ≫
      S.rightDerivedFunctorPlusCompatibility.inv.app (DerivedCategory.Plus.Qh.obj J) =
      DerivedCategory.Plus.ι.map (S.rightDerivedFunctorPlusUnith.app J) := by
    simpa only [rightDerivedFunctorPlusCompatibility, rightDerivedUnique,
      rightDerivedNatIso, ιRightDerivedFunctorUnit, rightDerivedFunctorPlusιUnit,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.id_app,
      Category.id_comp, Iso.refl_inv] using
      rightDerivedNatTrans_app (DerivedCategory.Plus.ι ⋙ S.rightDerivedFunctor)
        (S.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
        S.ιRightDerivedFunctorUnit S.rightDerivedFunctorPlusιUnit
        (HomotopyCategory.Plus.quasiIso C) (𝟙 _) J
  let HD := DerivedCategory.homologyFunctor D n
  let FK := (S.mapHomologicalComplex (.up ℤ)).obj K
  let h := DerivedCategory.cyclesChainMap n K
  let i := (HomologicalComplex.singleMapHomologicalComplex S (.up ℤ) n).inv.app Y
  let z := DerivedCategory.Q.map (i ≫ (S.mapHomologicalComplex (.up ℤ)).map h)
  let k := (FK.sc n).liftCycles (S.map (K.sc n).iCycles) (by
    change S.map (K.sc n).iCycles ≫ S.map (K.sc n).g = 0
    rw [← S.map_comp, (K.sc n).iCycles_g, S.map_zero])
  have hz : (DerivedCategory.singleFunctorCompHomologyFunctorIso D n).inv.app
        (S.obj Y) ≫ HD.map z =
      k ≫ (FK.sc n).homologyπ ≫
        (DerivedCategory.homologyFunctorFactors D n).inv.app FK := by
    have hh : i ≫ (S.mapHomologicalComplex (.up ℤ)).map h =
        (CochainComplex.singleFunctor D n).map k ≫
          DerivedCategory.cyclesChainMap n FK := by
      apply HomologicalComplex.from_single_hom_ext
      simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        DerivedCategory.cyclesChainMap, HomologicalComplex.mkHomFromSingle_f]
      dsimp only [i, h]
      simp only [DerivedCategory.cyclesChainMap, HomologicalComplex.mkHomFromSingle_f,
        HomologicalComplex.singleMapHomologicalComplex_inv_app_self, Functor.map_comp,
        Category.assoc]
      erw [← S.map_comp_assoc, Iso.inv_hom_id, S.map_id, Category.id_comp]
      erw [HomologicalComplex.single_map_f_self]
      simp only [Category.assoc]
      erw [Iso.inv_hom_id_assoc]
      change _ ≫ S.map (K.sc n).iCycles = _ ≫ k ≫ (FK.sc n).iCycles
      rw [ShortComplex.liftCycles_i]
    dsimp only [z]
    rw [hh, DerivedCategory.Q.map_comp, HD.map_comp]
    change (DerivedCategory.singleFunctorCompHomologyFunctorIso D n).inv.app
      (S.obj Y) ≫
      (DerivedCategory.singleFunctor D n ⋙ HD).map k ≫
      HD.map (DerivedCategory.Q.map (DerivedCategory.cyclesChainMap n FK)) = _
    erw [← reassoc_of%
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso D n).inv.naturality k)]
    have hcy := DerivedCategory.cyclesDerivedMap_homology n FK
    simp only [DerivedCategory.cyclesDerivedMap, DerivedCategory.singleFunctorIsoCompQ,
      Iso.refl_hom, NatTrans.id_app, Category.id_comp] at hcy
    simpa only [Functor.id_map, Category.assoc] using congrArg (fun a ↦ k ≫ a) hcy
  let f : (DerivedCategory.Plus.singleFunctor C n).obj Y ⟶ M :=
    DerivedCategory.Plus.ι.preimage (DerivedCategory.cyclesDerivedMap n K ≫ q)
  have he : (DerivedCategory.Plus.ι.preimageIso
        (X := (DerivedCategory.Plus.singleFunctor C n).obj Y)
        (Y := DerivedCategory.Plus.Qh.obj J)
        ((DerivedCategory.singleFunctorIsoCompQ C n).app Y ≪≫
          (DerivedCategory.quotientCompQhIso C).symm.app _)).inv = 𝟙 _ := by
    apply DerivedCategory.Plus.ι.map_injective
    simp only [Functor.preimageIso_inv, Functor.map_preimage, Iso.trans_inv,
      Functor.map_id]
    change (𝟙 _) ≫ (𝟙 _) = 𝟙 _
    exact Category.id_comp _
  have hs : DerivedCategory.Plus.ι.map (S.rightDerivedPlusSingleUnitAt n Y) =
      DerivedCategory.Q.map i ≫
        S.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj A) ≫
        S.rightDerivedFunctorPlusCompatibility.inv.app
          ((DerivedCategory.Plus.singleFunctor C n).obj Y) := by
    dsimp only [rightDerivedPlusSingleUnitAt]
    rw [he, S.rightDerivedFunctorPlus.map_id]
    erw [Category.comp_id]
    simp only [Functor.map_comp, mapHomotopyCategoryPlusSingleFunctorQhObjIso,
      Functor.preimageIso_inv, Functor.map_preimage]
    rw [← hcunit]
    simp only [Iso.trans_inv, Functor.mapIso_inv, Category.assoc]
    erw [Category.id_comp]
    rfl
  have hw : z ≫
      S.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) ≫
      S.rightDerivedFunctor.map q ≫ S.rightDerivedFunctorPlusCompatibility.inv.app M =
      DerivedCategory.Plus.ι.map (S.rightDerivedPlusSingleUnitAt n Y) ≫
        DerivedCategory.Plus.ι.map (S.rightDerivedFunctorPlus.map f) := by
    dsimp only [z]
    rw [DerivedCategory.Q.map_comp, Category.assoc]
    have hn := S.rightDerivedFunctorUnit.naturality
      ((HomotopyCategory.quotient C (.up ℤ)).map h)
    dsimp only [Functor.comp_map] at hn
    rw [Functor.mapHomotopyCategory_map] at hn
    change DerivedCategory.Q.map i ≫ DerivedCategory.Q.map
        ((S.mapHomologicalComplex (.up ℤ)).map h) ≫
      S.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) ≫
      S.rightDerivedFunctor.map q ≫ S.rightDerivedFunctorPlusCompatibility.inv.app M = _
    erw [reassoc_of% hn]
    rw [← S.rightDerivedFunctor.map_comp_assoc]
    have hloc : DerivedCategory.Qh.map
        ((HomotopyCategory.quotient C (.up ℤ)).map h) = DerivedCategory.Q.map h := by
      have ht := DerivedCategory.quotientCompQhIso_hom_naturality h
      change _ ≫ 𝟙 _ = 𝟙 _ ≫ _ at ht
      simpa only [Category.comp_id, Category.id_comp] using ht
    rw [hloc]
    have hcy : DerivedCategory.cyclesDerivedMap n K = DerivedCategory.Q.map h := by
      simp only [DerivedCategory.cyclesDerivedMap, DerivedCategory.singleFunctorIsoCompQ,
        Iso.refl_hom, NatTrans.id_app, Category.id_comp]
      rfl
    rw [← hcy]
    have hpre : DerivedCategory.Plus.ι.map f = DerivedCategory.cyclesDerivedMap n K ≫ q :=
      DerivedCategory.Plus.ι.map_preimage _
    rw [← hpre]
    change DerivedCategory.Q.map i ≫
      S.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj A) ≫
      S.rightDerivedFunctor.map (DerivedCategory.Plus.ι.map f) ≫
      S.rightDerivedFunctorPlusCompatibility.inv.app M = _
    erw [S.rightDerivedFunctorPlusCompatibility.inv.naturality f]
    rw [hs]
    simp only [Category.assoc]
    rfl
  change k ≫ (FK.sc n).homologyπ ≫
      (DerivedCategory.homologyFunctorFactors D n).inv.app FK ≫ _ = _
  rw [← reassoc_of% hz]
  erw [← HD.map_comp_assoc, ← HD.map_comp_assoc, ← HD.map_comp]
  simp only [Category.assoc]
  erw [Category.id_comp, S.rightDerivedFunctor.map_id, Category.id_comp]
  rw [hw]
  simp only [HD.map_comp, Category.assoc, rightDerivedPlusSingleUnitHomologyAt]
  rfl

end CategoryTheory.Functor
