/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Derived.DerivedScalarExtUnit

/-! # Degree-zero scalar Ext units
(blueprint: lem-sp-derived-scalar-ext-unit-zero).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe uC uB vC vB wC wB wE
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace CategoryTheory.Functor
variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B] [HasExt.{wE} B]
  (U : C ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]

/-- For exact additive U and η:F→UH with DerivedUnit [def-sp-exact-functor-derived-unit], the
degree-zero class mk0(η) has DerivedExtUnit [def-sp-derived-scalar-ext-unit].
Source: blueprint Cartier derived reduction and comparison paragraphs; Stacks 0152,
06YY and 0GLZ (blueprint: lem-sp-derived-scalar-ext-unit-zero).
Proof: The zero-shift functor is canonically isomorphic to the identity. Transfer the domain Hom set
through that isomorphism and use the given unit bijection. The zero-shift coherence for exact
derived functors and the formula for mk0 identify the transferred function with the displayed
degree-zero Ext unit. -/
theorem DerivedUnit.extUnit_zero {F : B} {H : C} {η : F ⟶ U.obj H}
    (h : U.DerivedUnit F H η) : U.DerivedExtUnit F H 0 (Ext.mk₀.{wE} η) := by
  unfold DerivedExtUnit DerivedUnit at *
  intro K
  let e := (shiftFunctorZero (DerivedCategory C) ℤ).app
    ((DerivedCategory.singleFunctor C 0).obj H)
  have hb := (h K).comp e.homFromEquiv.bijective
  have he (f : ((DerivedCategory.singleFunctor C 0).obj H)⟦(0 : ℤ)⟧ ⟶ K) :
      (Ext.mk₀.{wE} η).hom ≫
        ((U.mapDerivedCategorySingleFunctor 0).inv.app H)⟦(0 : ℤ)⟧' ≫
        (U.mapDerivedCategory.commShiftIso (0 : ℤ)).inv.app
          ((DerivedCategory.singleFunctor C 0).obj H) ≫ U.mapDerivedCategory.map f =
      (DerivedCategory.singleFunctor B 0).map η ≫
        (U.mapDerivedCategorySingleFunctor 0).inv.app H ≫
          U.mapDerivedCategory.map (e.inv ≫ f) := by
    simp only [Ext.mk₀_hom, ShiftedHom.mk₀, commShiftIso_zero,
      CommShift.isoZero_inv_app, Category.assoc]
    simp [shiftFunctorZero', ← Functor.map_comp, e]
  simp only [Function.comp_def, Iso.homFromEquiv_apply, ← he] at hb
  convert hb using 1
end CategoryTheory.Functor
