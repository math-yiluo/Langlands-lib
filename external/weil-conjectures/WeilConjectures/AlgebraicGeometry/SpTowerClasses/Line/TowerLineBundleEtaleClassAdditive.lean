/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassReduction
import WeilConjectures.AlgebraicGeometry.Sites.GmPicard

/-! # Additivity of the integral line class after change of site

Source: tower classes proof (2), Picard additivity and exact derived comparison.
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

private theorem mapExtensionEndpoints_add
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D] [HasExt.{w₃} C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y : C} {X' Y' : D} (e e' : Ext.{w₃} X Y 1)
    (a : X' ⟶ F.obj X) (b : F.obj Y ⟶ Y') :
    mapExtensionEndpoints F (e + e') a b =
      mapExtensionEndpoints F e a b + mapExtensionEndpoints F e' a b := by
  simp only [mapExtensionEndpoints, Ext.add_hom, mapSingleArrow_add,
    Preadditive.comp_add, Preadditive.add_comp]

/-- Tensor multiplication becomes addition in the integral line class after changing
from the etale site to the pro-etale site.

Source: tower classes proof (2), Picard-to-H1 additivity (lemma-cohomology-multiplicative-group--3).
(blueprint: lem-sfb-tower-line-bundle-etale-class-additive).

Proof: the Picard-to-H1 map is additive. Its Ext realization preserves sums;
exact derived change of site is additive, and pre- and postcomposition with the
fixed integer and units comparisons distribute over sums. The generic endpoint
transport lemma makes these comparisons without unfolding their constructions.
-/
theorem tower_lineBundleEtaleClass_mul (T : Scheme.{u}) (L M : T.Pic) :
    lineBundleEtaleClass T (L * M) =
      lineBundleEtaleClass T L + lineBundleEtaleClass T M := by
  simp only [lineBundleEtaleClass, Scheme.Pic.toCohomologicalPicardGroup_mul,
    mapExtensionEndpoints_add]

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
