/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.CountableTensorStructures

/-! # Tensor structures from countable coproducts

Source: Stacks Project, derived.tex, Tag 0G6E, signed direct-sum totalization;
Mathlib's graded-object and homological-complex monoidal constructions.
(blueprint: def-sfb-countable-tensor-structures)
-/

@[expose] public section

set_option autoImplicit false
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory

attribute [instance] TensorPreservesCountableCoproducts.left
  TensorPreservesCountableCoproducts.right

namespace CountableTensorStructures

variable {C : Type u} [Category.{v} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
  [TensorPreservesCountableCoproducts C]

/-- The standard Koszul braiding, with summand map `(-1)^(pq)` times the base braiding.
Source: `CochainComplex.Monoidal.braidedCategory`, Stacks Tag 0G6E
(blueprint: def-sfb-countable-tensor-structures). -/
noncomputable instance braided [BraidedCategory C] : BraidedCategory (CochainComplex C ℤ) :=
  CochainComplex.Monoidal.braidedCategory

end CountableTensorStructures
end CategoryTheory
