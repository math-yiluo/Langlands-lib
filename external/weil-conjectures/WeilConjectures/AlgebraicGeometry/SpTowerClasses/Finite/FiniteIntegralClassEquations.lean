/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassReduction

/-! # Evaluating the integral Kummer composite

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-integral-class-equations).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u u₁ v₁ u₂ v₂ w₁ w₂ t₁ t₂
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [local implicit_reducible] diagonalAbSheafAbelian towerAbelian constant

attribute [local irreducible] Functor.mapDerivedCategory Ext.homEquiv
  HasDerivedCategory.standard DerivedCategory.singleFunctors
  integerComparison cartierRootsComparison cartierUnitsComparison

/-- The line class uses the actual integer and units comparisons.
Source: the definition of lineBundleEtaleClass
(blueprint: lem-sfb-finite-integral-class-equations). -/
theorem finiteLineBundleEtaleClass_eq (T : Scheme.{u}) (L : T.Pic) :
    lineBundleEtaleClass T L =
      (DerivedCategory.singleFunctor (DiagonalAb T) 0).map (integerComparison T).inv ≫
        mapSingleArrow (comparisonUpperStar AddCommGrpCat.{u + 1} T) (1 : ℤ)
          (Scheme.Pic.toCohomologicalPicardGroup T L).hom ≫
        ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
          (cartierUnitsComparison T))⟦(1 : ℤ)⟧' := by rfl

end AlgebraicGeometry.ProEtale.SpTowerClasses
