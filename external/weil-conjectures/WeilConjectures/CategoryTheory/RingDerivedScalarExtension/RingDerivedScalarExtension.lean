/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement

/-! # Derived scalar extension for ordinary modules

Source: Stacks Project Tags 06YY and 07A6 (blueprint: def-zl-ring-derived-scalar-extension).

This module records the canonical ordinary-module derived restriction and its left
adjoint used by the condensed evaluation statement.  The underlying constructions are
those of the published constant-realization module, with no alternate choice of derived
functor.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe r wR wS wT

open CategoryTheory

namespace CategoryTheory.RingDerivedScalarExtension

/-- Derived restriction of scalars along a commutative ring homomorphism.

Source: Stacks Project Tag 07A6 (blueprint: def-zl-ring-derived-scalar-extension).
-/
abbrev moduleDerivedRestriction {A B : Type r} [CommRing A] [CommRing B]
    (f : A →+* B) [HasDerivedCategory.{wR} (ModuleCat.{r} A)]
    [HasDerivedCategory.{wS} (ModuleCat.{r} B)] :
    DerivedCategory (ModuleCat.{r} B) ⥤ DerivedCategory (ModuleCat.{r} A) :=
  ConstantScalarRealization.moduleDerivedRestriction.{wR, wS, r} f

/-- The derived restriction functor has the canonical right-adjoint structure.

Source: Stacks Project Tag 07A6 (blueprint: def-zl-ring-derived-scalar-extension).
-/
instance moduleDerivedRestriction_rightAdjoint {A B : Type r} [CommRing A] [CommRing B]
    (f : A →+* B) [HasDerivedCategory.{wR} (ModuleCat.{r} A)]
    [HasDerivedCategory.{wS} (ModuleCat.{r} B)] :
    (moduleDerivedRestriction f).IsRightAdjoint :=
  ConstantScalarRealization.moduleDerivedRestriction_rightAdjoint f

/-- Derived extension of scalars, fixed as the left adjoint of restriction.

Source: Stacks Project Tags 06YY and 07A6
(blueprint: def-zl-ring-derived-scalar-extension).
-/
def moduleDerivedExtension {A B : Type r} [CommRing A] [CommRing B]
    (f : A →+* B) [HasDerivedCategory.{wR} (ModuleCat.{r} A)]
    [HasDerivedCategory.{wS} (ModuleCat.{r} B)] :
    DerivedCategory (ModuleCat.{r} A) ⥤ DerivedCategory (ModuleCat.{r} B) :=
  (moduleDerivedRestriction f).leftAdjoint

end CategoryTheory.RingDerivedScalarExtension
