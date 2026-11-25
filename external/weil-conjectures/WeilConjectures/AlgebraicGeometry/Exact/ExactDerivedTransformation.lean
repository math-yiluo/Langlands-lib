/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-! # Natural transformations between exact derived functors
Source: localization universal property and naturality of the single comparisons.
(blueprint: lem-sfb-exact-derived-transformation). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

section
variable {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{v} B]
  {F G : A ⥤ B} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- Localize a termwise natural transformation between exact functors.
Source: localization universal property
(blueprint: lem-sfb-exact-derived-transformation). -/
def exactDerivedTransformation (τ : F ⟶ G) : F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex τ (.up ℤ)) DerivedCategory.Q)

/-- The localized transformation has the given termwise components.
Source: localization factorization
(blueprint: lem-sfb-exact-derived-transformation). -/
theorem exactDerivedTransformation_app (τ : F ⟶ G) (P : CochainComplex A ℤ) :
    (exactDerivedTransformation τ).app (DerivedCategory.Q.obj P) =
      F.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app P) ≫
          G.mapDerivedCategoryFactors.inv.app P := by
  simp only [exactDerivedTransformation, Localization.liftNatTrans_app,
    Functor.whiskerRight_app]
  rfl

/-- Termwise localization preserves compatibility with shifts.
Source: termwise shift compatibility and essential surjectivity of localization
(blueprint: lem-sfb-exact-derived-transformation). -/
instance exactDerivedTransformation_commShift (τ : F ⟶ G) :
    NatTrans.CommShift (exactDerivedTransformation τ) ℤ := by
  have heq : Functor.whiskerLeft DerivedCategory.Q (exactDerivedTransformation τ) =
      F.mapDerivedCategoryFactors.hom ≫
        Functor.whiskerRight (NatTrans.mapHomologicalComplex τ (.up ℤ)) DerivedCategory.Q ≫
        G.mapDerivedCategoryFactors.inv := by
    ext P
    exact exactDerivedTransformation_app τ P
  have : NatTrans.CommShift
      (Functor.whiskerLeft DerivedCategory.Q (exactDerivedTransformation τ)) ℤ := by
    rw [heq]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Q
    (fun X ↦ ⟨_, (DerivedCategory.Q.objObjPreimageIso X).inv, inferInstance⟩)

/-- The comparison for a single object is natural also in the exact functor.
Source: the single-complex comparison and localization factorization
(blueprint: lem-sfb-exact-derived-transformation). -/
theorem exactDerivedTransformation_single (τ : F ⟶ G) (M : A) :
    (exactDerivedTransformation τ).app ((DerivedCategory.singleFunctor A 0).obj M) ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app M =
      (F.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        (DerivedCategory.singleFunctor B 0).map (τ.app M) := by
  let K := (CochainComplex.singleFunctor A 0).obj M
  have hc (J : A ⥤ B) [J.Additive] [PreservesFiniteLimits J]
      [PreservesFiniteColimits J] :
      (J.mapDerivedCategorySingleFunctor 0).hom.app M =
        J.mapDerivedCategoryFactors.hom.app K ≫
          DerivedCategory.Q.map ((J.mapCochainComplexSingleFunctor 0).hom.app M) := by
    apply (cancel_epi (J.mapDerivedCategoryFactors.inv.app K)).1
    exact (J.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app M).trans
      (Iso.inv_hom_id_app_assoc J.mapDerivedCategoryFactors K
        (DerivedCategory.Q.map ((J.mapCochainComplexSingleFunctor 0).hom.app M))).symm
  have hn :
      (NatTrans.mapHomologicalComplex τ (.up ℤ)).app K ≫
        (G.mapCochainComplexSingleFunctor 0).hom.app M =
      (F.mapCochainComplexSingleFunctor 0).hom.app M ≫
        (CochainComplex.singleFunctor B 0).map (τ.app M) := by
    ext i
    by_cases hi : i = 0
    · subst i
      dsimp only [K, Functor.mapCochainComplexSingleFunctor]
      simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
        HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
      change τ.app (((HomologicalComplex.single A (.up ℤ) 0).obj M).X 0) ≫
        G.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (G.obj M)).inv =
        (F.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom ≫
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (F.obj M)).inv) ≫
            ((HomologicalComplex.single B (.up ℤ) 0).map (τ.app M)).f 0
      rw [HomologicalComplex.single_map_f_self]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      simpa only [Category.assoc] using congrArg (fun f ↦ f ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (G.obj M)).inv)
          (τ.naturality (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom).symm
    · have hz : IsZero (K.X i) := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi
      have hz' : IsZero ((F.mapHomologicalComplex (.up ℤ)).obj K |>.X i) :=
        F.map_isZero hz
      exact hz'.eq_of_src _ _
  have hcalc :
      (exactDerivedTransformation τ).app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategoryFactors.hom.app K ≫
          DerivedCategory.Q.map ((G.mapCochainComplexSingleFunctor 0).hom.app M) =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app M) ≫
          DerivedCategory.Q.map ((CochainComplex.singleFunctor B 0).map (τ.app M)) := by
    rw [exactDerivedTransformation_app]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
    exact congrArg (fun f ↦ F.mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map f) hn
  exact (congrArg (fun f ↦ (exactDerivedTransformation τ).app
    ((DerivedCategory.singleFunctor A 0).obj M) ≫ f) (hc G)).trans
    (hcalc.trans ((Category.assoc _ _ _).symm.trans
      (congrArg (fun f ↦ f ≫ (DerivedCategory.singleFunctor B 0).map (τ.app M)) (hc F)).symm))

/-- The exact-single comparison respects both a natural transformation and a shift.
Source: shift compatibility followed by the degree-zero single comparison
(blueprint: lem-sfb-exact-derived-transformation). -/
theorem exactDerivedTransformation_shiftedSingle (τ : F ⟶ G) (M : A) (r : ℤ) :
    (exactDerivedTransformation τ).app
        (((DerivedCategory.singleFunctor A 0).obj M)⟦r⟧) ≫
      (G.mapDerivedCategory.commShiftIso r).hom.app
        ((DerivedCategory.singleFunctor A 0).obj M) ≫
      ((G.mapDerivedCategorySingleFunctor 0).hom.app M)⟦r⟧' =
    (F.mapDerivedCategory.commShiftIso r).hom.app
        ((DerivedCategory.singleFunctor A 0).obj M) ≫
      ((F.mapDerivedCategorySingleFunctor 0).hom.app M)⟦r⟧' ≫
      ((DerivedCategory.singleFunctor B 0).map (τ.app M))⟦r⟧' := by
  rw [← Category.assoc, ← NatTrans.shift_app_comm,
    Category.assoc, ← Functor.map_comp, exactDerivedTransformation_single,
    Functor.map_comp]

end
end AlgebraicGeometry.ProEtale
