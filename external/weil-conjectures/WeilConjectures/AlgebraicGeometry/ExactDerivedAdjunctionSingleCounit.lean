/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Mathlib.Algebra.Homology.Localization

import all Mathlib.Algebra.Homology.Localization

/-! # The exact derived adjunction counit on a single complex

Source: Stacks Project, Tag 0AX3, derived trace as an adjunction counit.
(blueprint: lem-sc-exact-derived-adjunction-single-counit).
-/

@[expose] public section

universe uA uB vA vB wA wB

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Adjunction

variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasKInjectiveResolutions A] [HasKInjectiveResolutions B]

/-- The single comparison for an exact right adjoint preserves the derived counit.
Source: Stacks Project, Tag 0AX3, trace-map counit comparison
(blueprint: lem-sc-exact-derived-adjunction-single-counit).

Proof: Apply the factorization formula for the counit of the localized adjunction
at the homotopy image of L[0]. Replace the exact right-derived unit by the inverse
localization comparison, using its uniqueness factorization. The counit of the
homotopy adjunction is the quotient of the termwise counit. The single comparisons
identify this termwise counit with the single of the underived counit, by naturality
in the sole nonzero degree. Cancel the invertible exact-functor comparisons to obtain
the displayed equality. No faithfulness, nonzero object or boundedness is needed. -/
theorem exact_derivedAdjunction_single_counit {T : A ⥤ B} {H : B ⥤ A}
    [T.Additive] [H.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (adj : T ⊣ H) (L : B) :
    T.mapDerivedCategory.map (H.singleFunctorCompRightDerivedFunctorIso.inv.app L) ≫
      adj.mapDerivedCategoryRightDerivedAdjunction.counit.app
        ((DerivedCategory.singleFunctor B 0).obj L) =
    (T.mapDerivedCategorySingleFunctor 0).hom.app (H.obj L) ≫
      (DerivedCategory.singleFunctor B 0).map (adj.counit.app L) := by
  have : HasKInjectiveResolutions A := inferInstance
  have hunit (H : B ⥤ A) [H.Additive]
      [PreservesFiniteLimits H] [PreservesFiniteColimits H] (L : B) :
      H.singleFunctorCompRightDerivedFunctorIso.inv.app L =
        (H.mapDerivedCategorySingleFunctor 0).inv.app L ≫
        H.mapDerivedCategoryFactorsh.hom.app
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
            ((CochainComplex.singleFunctor B 0).obj L)) ≫
        H.rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
            ((CochainComplex.singleFunctor B 0).obj L)) := by
    let K := (HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor B 0).obj L)
    have hf := congr_app H.rightDerivedFunctorIsoMapDerivedCategory_hom_fac K
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
    have hu : H.mapDerivedCategoryFactorsh.hom.app K ≫
        H.rightDerivedFunctorUnit.app K =
        H.rightDerivedFunctorIsoMapDerivedCategory.inv.app (DerivedCategory.Qh.obj K) := by
      rw [← cancel_mono (H.rightDerivedFunctorIsoMapDerivedCategory.hom.app
        (DerivedCategory.Qh.obj K))]
      simp only [Category.assoc, hf, Iso.hom_inv_id_app, Iso.inv_hom_id_app]
      rfl
    dsimp only [Functor.singleFunctorCompRightDerivedFunctorIso, Iso.trans_inv,
      Functor.isoWhiskerLeft_inv, NatTrans.comp_app, Functor.whiskerLeft_app]
    exact congrArg ((H.mapDerivedCategorySingleFunctor 0).inv.app L ≫ ·) hu.symm
  have hterm {T : A ⥤ B} {H : B ⥤ A}
      [T.Additive] [H.Additive]
      [PreservesFiniteLimits T] [PreservesFiniteColimits T]
      [PreservesFiniteLimits H] [PreservesFiniteColimits H]
      (adj : T ⊣ H) (L : B) :
      T.mapDerivedCategory.map
        ((H.mapDerivedCategorySingleFunctor 0).inv.app L ≫
          H.mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
              ((CochainComplex.singleFunctor B 0).obj L))) ≫
        T.mapDerivedCategoryFactorsh.hom.app
          ((H.mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
              ((CochainComplex.singleFunctor B 0).obj L))) ≫
        DerivedCategory.Qh.map
          ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).counit.app
            ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
              ((CochainComplex.singleFunctor B 0).obj L))) =
      (T.mapDerivedCategorySingleFunctor 0).hom.app (H.obj L) ≫
        (DerivedCategory.singleFunctor B 0).map (adj.counit.app L) := by
    have hT := T.mapDerivedCategoryFactorsh_hom_app
      ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor B 0).obj L))
    rw [adj.mapHomotopyCategory_counit_app_quotient (ComplexShape.up ℤ),
      H.mapDerivedCategoryFactorsh_hom_app]
    erw [hT]
    simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
      Functor.map_comp, Category.assoc]
    simp only [Functor.comp_obj, Functor.map_id, Category.id_comp, cancelIso]
    rw [← DerivedCategory.quotientCompQhIso_inv_naturality]
    have hq : (DerivedCategory.quotientCompQhIso B).hom.app
        ((CochainComplex.singleFunctor B 0).obj L) = 𝟙 _ := rfl
    have hqi : (DerivedCategory.quotientCompQhIso B).inv.app
        ((CochainComplex.singleFunctor B 0).obj L) = 𝟙 _ := rfl
    simp only [Functor.id_obj, hq, hqi, Category.comp_id]
    simp only [Functor.comp_obj, Functor.map_id]
    erw [Functor.map_id, Category.id_comp]
    rw [← Functor.map_comp_assoc]
    erw [
      Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app]
    erw [Functor.mapDerivedCategoryFactors_hom_naturality_assoc]
    rw [← cancel_epi (T.mapDerivedCategoryFactors.inv.app
      ((CochainComplex.singleFunctor A 0).obj (H.obj L)))]
    simp only [Iso.inv_hom_id_app_assoc]
    erw [Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app_assoc]
    change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ =
      DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map
        ((CochainComplex.singleFunctor B 0).map (adj.counit.app L))
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    apply HomologicalComplex.hom_ext
    intro n
    by_cases hn : n = 0
    · subst n
      simp only [CochainComplex.singleFunctor, Functor.comp_obj,
        Functor.id_obj, Functor.mapCochainComplexSingleFunctor,
        HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
        HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
        eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp,
        mapHomologicalComplex_counit_app_f, counit_naturality,
        HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
        Functor.map_id, HomologicalComplex.single_map_f_self]
      erw [Category.id_comp]
    · simp [Functor.mapCochainComplexSingleFunctor,
        CochainComplex.singleFunctor,
        HomologicalComplex.singleMapHomologicalComplex_hom_app_ne,
        HomologicalComplex.singleMapHomologicalComplex_inv_app_ne, hn]
  have hfac := (adj.mapHomotopyCategory (ComplexShape.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))
    T.mapDerivedCategoryFactorsh.hom H.rightDerivedFunctorUnit
    ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor B 0).obj L))
  rw [hunit H L]
  simp only [Functor.map_comp, Category.assoc]
  rw [show T.mapDerivedCategory.map (H.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor B 0).obj L))) ≫
      adj.mapDerivedCategoryRightDerivedAdjunction.counit.app
        ((DerivedCategory.singleFunctor B 0).obj L) = _ from hfac]
  simpa only [Functor.map_comp, Category.assoc] using
    hterm adj L

end CategoryTheory.Adjunction
