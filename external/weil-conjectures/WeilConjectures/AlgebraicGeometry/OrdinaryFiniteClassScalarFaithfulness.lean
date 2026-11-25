/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Kummer

/-! # Scalar faithfulness of a specified ordinary cohomology class

Source: the normalized Kummer-class comparison in lemma-cohomology-projective-line-trace.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors CategoryTheory.Abelian.Ext.homEquiv
  CategoryTheory.Abelian.Ext.comp CategoryTheory.Abelian.Ext.mk₀
  CategoryTheory.Abelian.Ext.mapExactFunctor

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem kummer_classCore_zero
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasExt.{u + 1} C] [HasExt.{u + 1} D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {X : C} {Z : D} (e : Z ⟶ G.obj X) (Y : C) (n : ℕ) :
    ordinaryFiniteClassCore G e Y n 0 = 0 := by
  unfold ordinaryFiniteClassCore ordinaryFiniteExtClassCore
  change (CategoryTheory.Abelian.Ext.mk₀ e).comp
    ((CategoryTheory.Abelian.Ext.homAddEquiv.symm 0).mapExactFunctor G) (zero_add n) = 0
  rw [map_zero, CategoryTheory.Abelian.Ext.mapExactFunctor_zero,
    CategoryTheory.Abelian.Ext.comp_zero]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem kummer_classCore_precompose_scalar
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasExt.{u + 1} C] [HasExt.{u + 1} D]
    (R : Type*) [CommRing R] [Linear R C]
    (U : C ⥤ D) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {X Y : C} {Z : D} (e : Z ⟶ U.obj X) (n : ℕ)
    (c : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧) (a : R) :
    ordinaryFiniteClassCore U e Y n
        ((DerivedCategory.singleFunctor C 0).map (a • 𝟙 X) ≫ c) =
      (ordinaryFiniteClassCore U e Y n c).comp
        (CategoryTheory.Abelian.Ext.mk₀ (U.map (a • 𝟙 Y))) (add_zero n) := by
  let x := CategoryTheory.Abelian.Ext.homEquiv.symm c
  have hh : CategoryTheory.Abelian.Ext.homEquiv.symm
      ((DerivedCategory.singleFunctor C 0).map (a • 𝟙 X) ≫ c) =
      (CategoryTheory.Abelian.Ext.mk₀ (a • 𝟙 X)).comp x (zero_add n) := by
    apply CategoryTheory.Abelian.Ext.homEquiv.injective
    change _ = ((CategoryTheory.Abelian.Ext.mk₀ (a • 𝟙 X)).comp x (zero_add n)).hom
    simp only [CategoryTheory.Abelian.Ext.comp_hom, CategoryTheory.Abelian.Ext.mk₀_hom,
      ShiftedHom.mk₀_comp]
    rw [show x.hom = c from CategoryTheory.Abelian.Ext.homEquiv.apply_symm_apply c]
    exact CategoryTheory.Abelian.Ext.homEquiv.apply_symm_apply _
  have ha : (CategoryTheory.Abelian.Ext.mk₀ (a • 𝟙 X)).comp x (zero_add n) =
      x.comp (CategoryTheory.Abelian.Ext.mk₀ (a • 𝟙 Y)) (add_zero n) := by
    rw [CategoryTheory.Abelian.Ext.mk₀_smul, CategoryTheory.Abelian.Ext.smul_comp,
      CategoryTheory.Abelian.Ext.mk₀_id_comp,
      ← CategoryTheory.Abelian.Ext.smul_eq_comp_mk₀]
  unfold ordinaryFiniteClassCore ordinaryFiniteExtClassCore
  rw [hh, ha, CategoryTheory.Abelian.Ext.mapExactFunctor_comp,
    CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀,
    CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem kummer_core_class_scalar_faithful
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasExt.{u + 1} C] [HasExt.{u + 1} D]
    (R : Type*) [CommRing R] [Linear R C]
    (U : C ⥤ D) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    {X Y : C} {Z : D} (e : Z ⟶ U.obj X) (n : ℕ)
    (c : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧)
    (κ : CategoryTheory.Abelian.Ext.{u + 1} Z (U.obj Y) n)
    (hc : ordinaryFiniteClassCore U e Y n c = κ)
    (hκ : Function.Injective (fun a : R ↦ κ.comp
      (CategoryTheory.Abelian.Ext.mk₀ (U.map (a • 𝟙 Y))) (add_zero n))) :
    ∀ a : R, (DerivedCategory.singleFunctor C 0).map (a • 𝟙 X) ≫ c = 0 → a = 0 := by
  intro a ha
  apply hκ
  calc
    _ = ordinaryFiniteClassCore U e Y n
        ((DerivedCategory.singleFunctor C 0).map (a • 𝟙 X) ≫ c) := by
      rw [kummer_classCore_precompose_scalar, hc]
    _ = 0 := by rw [ha, kummer_classCore_zero]
    _ = _ := by
      simp only [zero_smul, U.map_zero, CategoryTheory.Abelian.Ext.mk₀_zero,
        CategoryTheory.Abelian.Ext.comp_zero]

/-- An injective scalar orbit of a normalized cohomology class detects scalar
annihilators of its specified derived representative.
Source: the Ext construction of ordinaryFiniteClass and blueprint
lemma-cohomology-projective-line-trace, geometric-fibre Kummer-class calculation.
(auxiliary; not a blueprint node).

Proof: precomposing the derived representative by a scalar equals postcomposing
its Ext class by that scalar. The exact forgetful functor preserves this identity,
and composition with the integral generator gives the cohomology action in the
statement. A vanishing composite therefore makes the scalar orbit equal its value
at zero. Injectivity of the orbit forces the scalar to be zero. The argument needs
neither finiteness nor a nonzero coefficient ring. -/
theorem ordinaryFiniteClass_scalar_faithful
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (c : ordinaryFiniteUnit A T ⟶ ((DerivedCategory.singleFunctor _ 0).obj F)⟦(2 : ℤ)⟧)
    (κ : Sheaf.H ((moduleAbelianForget A T).obj F) 2)
    (hc : ordinaryFiniteClass A T F 2 c = κ)
    (hκ : Function.Injective (fun a : A ↦ Sheaf.H.map
      ((moduleAbelianForget A T).map (a • 𝟙 F)) 2 κ)) :
    ∀ a : A, (DerivedCategory.singleFunctor _ 0).map
      (a • 𝟙 (ordinaryFiniteConstant A T)) ≫ c = 0 → a = 0 := by
  unfold ordinaryFiniteClass at hc
  apply kummer_core_class_scalar_faithful A (moduleAbelianForget A T)
    (ordinaryFiniteIntegralGenerator A T) 2 c κ hc
  intro a b hab
  apply hκ
  simpa only [Sheaf.H.map_apply] using hab

end AlgebraicGeometry.Etale
