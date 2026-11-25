/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassReduction
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.FiniteExactArrow.FiniteExactArrowCalculus

/-! # Realization of the ordinary scalar class

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-ordinary-scalar-class).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃ t₁ t₂ t₃
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses SpTowerClasses.FiniteExactArrow

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
attribute [local instance 100000] Etale.ordinaryFiniteDerivedCategoryInstance
attribute [local irreducible] Functor.mapDerivedCategory Ext.homEquiv
  HasDerivedCategory.standard DerivedCategory.singleFunctors

private theorem scalar_class_hom
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} D]
    [HasExt.{u + 1} C] [HasExt.{u + 1} D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {X Y : C} {Z : D} (e : Z ⟶ G.obj X)
    (a : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(2 : ℤ)⟧) :
    (Etale.ordinaryFiniteExtClassCore G e Y 2 (Ext.homEquiv.symm a)).hom =
      (DerivedCategory.singleFunctor D 0).map e ≫ mapSingleArrow G (2 : ℤ) a := by
  unfold Etale.ordinaryFiniteExtClassCore
  rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp,
    ← mapSingleArrow_ext G (n := 2)]
  rw [show (Ext.homEquiv.symm a).hom = a from Ext.homEquiv.apply_symm_apply a]
  rfl

/-- Realizing the ordinary scalar class is exact forgetting preceded by the
integral generator. Source: Stacks 03FD and the definition of ordinaryFiniteClass
(blueprint: lem-sfb-finite-ordinary-scalar-class). -/
theorem ordinaryFiniteClass_hom (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (a : Etale.ordinaryFiniteUnit A T ⟶
      ((DerivedCategory.singleFunctor _ 0).obj M)⟦(2 : ℤ)⟧) :
    (Etale.ordinaryFiniteClass A T M 2 a).hom =
      (DerivedCategory.singleFunctor _ 0).map (Etale.ordinaryFiniteIntegralGenerator A T) ≫
        mapSingleArrow (Etale.moduleAbelianForget A T) (2 : ℤ) a := by
  rw [Etale.ordinaryFiniteClass, Etale.ordinaryFiniteExtHomEquiv_eq]
  exact scalar_class_hom (Etale.moduleAbelianForget A T)
    (Etale.ordinaryFiniteIntegralGenerator A T) a

end AlgebraicGeometry.ProEtale.DiagonalTrace
