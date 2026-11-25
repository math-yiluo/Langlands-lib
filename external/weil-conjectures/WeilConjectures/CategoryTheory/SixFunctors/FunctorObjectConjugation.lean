/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! Conjugating a functor by an arbitrary family of object automorphisms.
Source: Mathlib's definition of a functor and natural isomorphism; the change of
presentation in Zheng, Construction 5.25.
(blueprint: lem-sf-functor-comparison-normalization)
-/

@[expose] public section
set_option autoImplicit false
universe v₁ v₂ v₃ u₁ u₂ u₃
namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  (F : A ⥤ B)

end CategoryTheory.Functor
