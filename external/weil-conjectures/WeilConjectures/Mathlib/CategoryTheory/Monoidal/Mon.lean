/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mon

/-!

# Transport of commutativity of monoid objects along isomorphisms

Mathlib transports the structure of a monoid object along an isomorphism `e : M ≅ N`
(`MonObj.ofIso`) and shows that `e.hom` is then a morphism of monoid objects. This file
adds that the transported monoid object is commutative when the original one is.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj

namespace CategoryTheory.IsCommMonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The monoid object structure transported along an isomorphism `e : M ≅ N` from a commutative
monoid object `M` is commutative: the braiding of `N` is conjugate to that of `M`. -/
lemma ofIso {M N : C} [MonObj M] [IsCommMonObj M] (e : M ≅ N) :
    letI := MonObj.ofIso e
    IsCommMonObj N := by
  let := MonObj.ofIso e
  constructor
  rw [MonObj.ofIso_mul, ← Category.assoc, ← BraidedCategory.braiding_naturality,
    Category.assoc, IsCommMonObj.mul_comm_assoc]

end CategoryTheory.IsCommMonObj
