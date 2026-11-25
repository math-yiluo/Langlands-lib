/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorConj
public import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonExt
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-! # Equivalences for finite étale comparison -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u wB
open CategoryTheory CategoryTheory.Abelian
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
attribute [local irreducible] CategoryTheory.Abelian.Ext Ext.comp Ext.mk₀
  Ext.mk₀CompMk₀ Ext.mapExactFunctor comparisonUpperStar

/-- Transport an Ext class through isomorphisms of its two endpoints.
Source: functoriality of Ext (blueprint: def-sfb-diagonal-trace-finite-etale-comparison). -/
def finiteExtEndpointEquiv
    {C : Type*} [Category C] [Abelian C] [HasExt.{wB} C]
    {X X' Y Y' : C} (a : X ≅ X') (b : Y ≅ Y') :
    Ext.{wB} X Y 2 ≃ Ext.{wB} X' Y' 2 where
  toFun v := Ext.mk₀CompMk₀ a.inv v b.hom
  invFun v := Ext.mk₀CompMk₀ a.hom v b.inv
  left_inv v := by
    change Ext.mk₀CompMk₀ a.hom (Ext.mk₀CompMk₀ a.inv v b.hom) b.inv = v
    rw [Ext.mk₀CompMk₀_mk₀CompMk₀]
    simp only [Iso.hom_inv_id, Ext.mk₀CompMk₀_id]
  right_inv v := by
    change Ext.mk₀CompMk₀ a.inv (Ext.mk₀CompMk₀ a.hom v b.inv) b.hom = v
    rw [Ext.mk₀CompMk₀_mk₀CompMk₀]
    simp only [Iso.inv_hom_id, Ext.mk₀CompMk₀_id]

/-- The exact site-comparison equivalence on finite Ext classes.
Its inverse is determined uniquely by the proved comparison bijection.
Source: exact étale-to-pro-étale Ext comparison.
(blueprint: def-sfb-diagonal-trace-finite-etale-comparison). -/
@[irreducible] def finiteEtaleRawEquiv (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) :
    Ext (Etale.ordinaryFiniteConstant A T) (Scheme.finiteEtaleTateLine T N A hA) 2 ≃
    Ext ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
      (Etale.ordinaryFiniteConstant A T))
      ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
        (Scheme.finiteEtaleTateLine T N A hA)) 2 :=
  Equiv.ofBijective _ (comparison_mapExt_bijective (ModuleCat.{u + 1} A) T _ _ 2)

end AlgebraicGeometry.ProEtale.DiagonalTrace
