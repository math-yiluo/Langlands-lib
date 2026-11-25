/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassReduction

/-! # Underlying single-to-shifted-single arrows in arbitrary categories -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u₁ v₁ u₂ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- Apply exact forgetting between prescribed source and target maps.
Source: blueprint latest, geometric classes proof, clause (2).
(blueprint: def-sfb-underlying-single-arrow).
This is the actual composite of the single source map, exact transport and
shifted single target map, constructed before specializing either category. -/
@[irreducible] def underlyingSingleArrow
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {X Y : C} {I J : D} (q : I ⟶ G.obj X) (y : G.obj Y ⟶ J)
    (f : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(2 : ℤ)⟧) :
    (DerivedCategory.singleFunctor D 0).obj I ⟶
      ((DerivedCategory.singleFunctor D 0).obj J)⟦(2 : ℤ)⟧ :=
  (DerivedCategory.singleFunctor D 0).map q ≫ mapSingleArrow G (2 : ℤ) f ≫
    ((DerivedCategory.singleFunctor D 0).map y)⟦(2 : ℤ)⟧'

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
