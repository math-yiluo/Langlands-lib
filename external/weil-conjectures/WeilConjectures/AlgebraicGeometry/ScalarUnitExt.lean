/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import WeilConjectures.AlgebraicGeometry.ExactFunctorDerivedUnit
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe uC uB vC vB wC wB hC hB
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace CategoryTheory.Abelian

/-- For exact additive U:A→B, η:F→UP with the unbounded derived unit property
[def-sp-exact-functor-derived-unit], Q in A and n≥0, the map Ext^n(P,Q)→Ext^n(F,UQ) sending c to
mk0(η) composed with U(c) is bijective [def-weil-abstract-derived-category].
Source: blueprint Cartier derived reduction and comparison paragraphs; Stacks 0152,
06YY and 0GLZ (auxiliary; not a blueprint node).
Proof: Test the unit universal property at (single Q)[n]. Identify Hom sets with Ext using
Ext.homEquiv. Naturality of the exact-functor single comparison and its commutation with shift
identifies the resulting function with the stated Yoneda composition. -/
theorem scalar_unit_ext_bijective
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{wC} C]
    [HasDerivedCategory.{hC} C]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasExt.{wB} B]
    [HasDerivedCategory.{hB} B]
    (U : C ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {F : B} {P Q : C} (η : F ⟶ U.obj P)
    (hη : U.DerivedUnit F P η)
    (n : ℕ) :
    Function.Bijective (fun c : Ext.{wC} P Q n ↦
      (Ext.mk₀.{wB} η).comp (Ext.mapExactFunctor.{wC, wB} U c) (zero_add n)) := by
  unfold Functor.DerivedUnit at hη
  let sC := DerivedCategory.singleFunctor C 0
  let sB := DerivedCategory.singleFunctor B 0
  let e : U.mapDerivedCategory.obj ((sC.obj Q)⟦(n : ℤ)⟧) ≅
      (sB.obj (U.obj Q))⟦(n : ℤ)⟧ :=
    (U.mapDerivedCategory.commShiftIso (n : ℤ)).app (sC.obj Q) ≪≫
      (shiftFunctor _ (n : ℤ)).mapIso ((U.mapDerivedCategorySingleFunctor 0).app Q)
  have hb := (Iso.homCongr (Iso.refl (sB.obj F)) e).bijective.comp
    ((hη ((sC.obj Q)⟦(n : ℤ)⟧)).comp Ext.homEquiv.bijective)
  have heq (c : Ext.{wC} P Q n) :
      ((Ext.mk₀.{wB} η).comp (Ext.mapExactFunctor.{wC, wB} U c) (zero_add n)).hom =
        (DerivedCategory.singleFunctor B 0).map η ≫
          (U.mapDerivedCategorySingleFunctor 0).inv.app P ≫
            U.mapDerivedCategory.map c.hom ≫ e.hom := by
    rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp, Ext.mapExactFunctor_hom]
    simp only [ShiftedHom.map, e, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom, Category.assoc]
    rfl
  have hh : Function.Bijective (fun c : Ext.{wC} P Q n ↦
      ((Ext.mk₀.{wB} η).comp (Ext.mapExactFunctor.{wC, wB} U c) (zero_add n)).hom) := by
    have hh := hb
    change Function.Bijective (fun c : Ext.{wC} P Q n ↦
      (𝟙 _) ≫ ((sB.map η ≫ (U.mapDerivedCategorySingleFunctor 0).inv.app P ≫
        U.mapDerivedCategory.map c.hom) ≫ e.hom)) at hh
    simpa only [Category.id_comp, Category.assoc, heq] using hh
  exact (Function.Bijective.of_comp_iff' Ext.homEquiv.bijective _).mp hh

end CategoryTheory.Abelian
