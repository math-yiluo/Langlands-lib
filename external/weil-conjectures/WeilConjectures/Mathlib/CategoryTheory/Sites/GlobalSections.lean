/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian

/-!
# Additivity of the global sections functor

The global sections functor `Sheaf.Γ J A` of `Mathlib.CategoryTheory.Sites.GlobalSections` is
right adjoint to the constant sheaf functor (`CategoryTheory.constantSheafΓAdj`), which is
additive when `A` is abelian and sheafification exists
(`Mathlib.CategoryTheory.Sites.Abelian`). Hence `Sheaf.Γ J A` is additive as well, and linear
over any ring over which `A` is linear.

This file imports both `Mathlib.CategoryTheory.Sites.Abelian` and
`Mathlib.CategoryTheory.Sites.GlobalSections` since neither imports the other.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)
  (A : Type*) [Category* A] [Abelian A] [HasSheafify J A] [HasGlobalSectionsFunctor J A]

/-- The global sections functor on sheaves with values in an abelian category is
additive, being right adjoint to the additive constant sheaf functor. -/
instance Sheaf.Γ_additive : (Sheaf.Γ J A).Additive :=
  (constantSheafΓAdj J A).right_adjoint_additive

/-- The global sections functor on sheaves with values in an `R`-linear abelian category is
`R`-linear, being right adjoint to the `R`-linear constant sheaf functor. -/
instance Sheaf.Γ_linear (R : Type*) [Semiring R] [Linear R A] : (Sheaf.Γ J A).Linear R :=
  (constantSheafΓAdj J A).right_adjoint_linear

end CategoryTheory
