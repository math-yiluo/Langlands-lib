/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite

/-! # Evaluating the integral Kummer composite

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: def-sfb-finite-integral-category-witnesses).
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

/-- The existing tower localization, with its functor category written explicitly.
Source: the integral tower category
(blueprint: def-sfb-finite-integral-category-witnesses). -/
@[instance_reducible]
def finiteIntegralTowerDerived (T : Scheme.{u}) :
    HasDerivedCategory.{u + 2} (ℕᵒᵖ ⥤ DiagonalAb T) := abDerived T

/-- The existing tower Ext witness at the same universe.
Source: integral tower Ext
(blueprint: def-sfb-finite-integral-category-witnesses). -/
theorem finiteIntegralTowerExt (T : Scheme.{u}) :
    HasExt.{u + 2} (ℕᵒᵖ ⥤ DiagonalAb T) := abExt T

/-- The existing small localization of pro-etale abelian sheaves.
Source: Grothendieck abelian sheaves
(blueprint: def-sfb-finite-integral-category-witnesses). -/
@[instance_reducible]
def finiteIntegralAbDerived (T : Scheme.{u}) :
    HasDerivedCategory.{u + 1} (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) :=
  inferInstance

attribute [local instance 100001] finiteIntegralAbDerived

/-- The corresponding small Ext witness on pro-etale abelian sheaves.
Source: the chosen small localization
(blueprint: def-sfb-finite-integral-category-witnesses). -/
theorem finiteIntegralAbExt (T : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) :=
  hasExt_of_hasDerivedCategory _

/-- The existing small localization of etale abelian sheaves.
Source: Grothendieck abelian sheaves on the small etale site
(blueprint: def-sfb-finite-integral-category-witnesses). -/
@[instance_reducible]
def finiteIntegralEtaleDerived (T : Scheme.{u}) :
    HasDerivedCategory.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  inferInstance

attribute [local instance 100001] finiteIntegralEtaleDerived

/-- Small Ext on etale abelian sheaves in that localization.
Source: the chosen small localization
(blueprint: def-sfb-finite-integral-category-witnesses). -/
theorem finiteIntegralEtaleExt (T : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  hasExt_of_hasDerivedCategory _

/-- The actual evaluated integral degree-one arrow type, named before its maps.
Source: exact evaluation of constant integer and units towers
(blueprint: def-sfb-finite-integral-category-witnesses). -/
def FiniteIntegralEvaluatedLineArrow (T : Scheme.{u}) (n : ℕ) :=
  (DerivedCategory.singleFunctor (DiagonalAb T) 0).obj
      ((abEvaluation T n).obj (integers T)) ⟶
    ((DerivedCategory.singleFunctor (DiagonalAb T) 0).obj
      ((units T).obj (op n)))⟦(1 : ℤ)⟧

/-- The actual evaluated integral boundary arrow type, shared by both composites.
Source: the fixed integral and roots endpoints at a finite level
(blueprint: def-sfb-finite-integral-category-witnesses). -/
def FiniteIntegralBoundaryArrow (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) (n : ℕ) :=
  (DerivedCategory.singleFunctor (DiagonalAb T) 0).obj
      ((abEvaluation T n).obj (integers T)) ⟶
    ((DerivedCategory.singleFunctor (DiagonalAb T) 0).obj
      ((roots l T).obj (op n)))⟦(2 : ℤ)⟧

end AlgebraicGeometry.ProEtale.SpTowerClasses
