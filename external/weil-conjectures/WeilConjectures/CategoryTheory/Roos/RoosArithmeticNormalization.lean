/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.Strict.StrictRoosDerivedLimitComparisonSupplement
public import WeilConjectures.CategoryTheory.StrictTowerArithmetic.StrictTowerArithmeticRestrictionDefs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import all WeilConjectures.CategoryTheory.SmoothPurity.CompactSupportRoosCofinality
import all WeilConjectures.CategoryTheory.Strict.StrictRoosDerivedLimitComparisonSupplement

/-! # Arithmetic normalization of a unit-normalized Roos comparison

The selection/block coordinate formula fixes the derived restriction map and
its value on every strict augmentation. Source: Stacks 0941
(blueprint: lem-pur-roos-arithmetic-normalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

attribute [local implicit_reducible] CategoryTheory.roosF CategoryTheory.roosConeFunctor
  CategoryTheory.strictRoosComplex CategoryTheory.strictRoosEndomorphism
  CategoryTheory.strictRoosProduct HomologicalComplex.asFunctor
  HomologicalComplex.complexOfFunctorsToFunctorToComplex
  CategoryTheory.NatTrans.mapHomologicalComplex
  HomologicalComplex.coneOfHasLimitEval CategoryTheory.strictTowerLimitIso

universe v w d
variable {A : Type v} [Category.{w} A] [Abelian A] [HasCountableProducts A]
  [HasLimitsOfShape ℕᵒᵖ A]

section DerivedComparison

variable [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ A)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
  [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive]

end DerivedComparison

variable [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ A)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
  [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive]

end CategoryTheory
