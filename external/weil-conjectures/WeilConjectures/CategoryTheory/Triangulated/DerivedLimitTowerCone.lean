/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-! # Limit of a tower of cochain complexes
Source: Mathlib, CategoryTheory.Limits.hasLimit_of_equalizer_and_product
(blueprint: lem-weil-derived-limit-tower-core-cone). -/

@[expose] public section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex

/-- A tower of cochain complexes in an abelian category with countable products has a limit.
Source: Mathlib, `Limits.hasLimit_of_equalizer_and_product` (Stacks Tag 002N).
Proof: countable products in `A` induce countable products of cochain complexes.
The object and arrow index types of the natural-number tower are countable.
An abelian category of complexes has equalizers. Mathlib's construction of a
limit as an equalizer of two product maps therefore supplies a limit cone.
(blueprint: lem-weil-derived-limit-tower-core-cone). -/
theorem hasLimit_asFunctor (A : Type u) [Category.{v} A] [Abelian A]
    [HasCountableProducts A] (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : HasLimit I.asFunctor := by
  have : HasCountableProducts (CochainComplex A ℤ) := ⟨fun _ ↦ inferInstance⟩
  exact hasLimit_of_equalizer_and_product I.asFunctor

end CochainComplex
