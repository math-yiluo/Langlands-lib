/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassReduction
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Line.TowerLineBundleEtaleClassAdditive

/-! # Additivity of the integral line class as a constant tower

Source: tower classes proof (2), exact constant-tower realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u u₁ v₁ u₂ v₂ w₁ w₂ w₃
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [local irreducible] Functor.mapDerivedCategory lineBundleEtaleClass lineBundleClass
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

private theorem mapSingleArrow_add
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y : C} (n : ℤ)
    (f g : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦n⟧) :
    mapSingleArrow F n (f + g) = mapSingleArrow F n f + mapSingleArrow F n g := by
  simp only [mapSingleArrow, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

/-- Tensor multiplication becomes addition for the integral line class in the
ordinary derived category of constant towers.

Source: tower classes proof (2), constant-system realization of the Picard class.
(blueprint: lem-sfb-tower-line-bundle-class-additive).

Proof: the changed-site integral line class preserves multiplication as addition
by tower_lineBundleEtaleClass_mul. The constant-system functor is exact and
additive. Its derived functor therefore preserves the sum, and the fixed single
and shift comparisons preserve it under composition. This is precisely the
mapSingleArrow transport defining lineBundleClass.
-/
theorem tower_lineBundleClass_mul (T : Scheme.{u}) (L M : T.Pic) :
    lineBundleClass T (L * M) = lineBundleClass T L + lineBundleClass T M := by
  simp only [lineBundleClass, tower_lineBundleEtaleClass_mul, mapSingleArrow_add]

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
