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

/-!
# The termwise product functor on strict tower complexes

Source: Stacks Project, sites-cohomology.tex, Tag 0941, proof of
lemma-derived-limit-is-ok, the termwise product of evaluated tower complexes.
(blueprint: def-pur-tower-product-functor)

This packages the existing `roosP` and `roosPmap` as a functor, using their
existing identity and composition laws. No shift comparison is part of this definition.
-/

@[expose] public section

set_option autoImplicit false

universe a b

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.InjectiveTowerRoos

variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]

/-- The product of the evaluated complexes of a strict tower complex, acting on
strict maps by the product of their evaluated maps.
Source: Stacks Project, sites-cohomology.tex, Tag 0941, proof of
lemma-derived-limit-is-ok (blueprint: def-pur-tower-product-functor). -/
noncomputable def productFunctor :
    CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ where
  obj := roosP
  map := roosPmap
  map_id := roosPmap_id
  map_comp := roosPmap_comp

end CategoryTheory.InjectiveTowerRoos
