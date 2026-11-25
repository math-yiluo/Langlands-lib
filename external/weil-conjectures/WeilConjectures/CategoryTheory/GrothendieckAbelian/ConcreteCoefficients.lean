/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Coefficients

/-!

# Concrete coefficient categories have small-site sheafification

A category `A` with `Hom`-types in `Type (u + 1)`, concrete over `Type (u + 1)` with a
forgetful functor that preserves limits and filtered colimits of size `u + 1` and reflects
isomorphisms, has small-site sheafification (`CategoryTheory.HasSmallSiteSheafify`): for a
`u + 1`-small site, the covering sieves of an object form a category of size `u + 1`, so
Mathlib's plus-construction (`Mathlib/CategoryTheory/Sites/LeftExact.lean`) produces a left
exact sheafification.

In particular the intended coefficient categories `ModuleCat.{u + 1} Λ` and
`AddCommGrpCat.{u + 1}` have small-site sheafification, and they are Grothendieck abelian of
size `u + 1` (Mathlib), so the sheaf categories on the small sites of `P`-schemes over
`Scheme.{u}` with these coefficients are Grothendieck abelian by
`CategoryTheory.GrothendieckTopology.isGrothendieckAbelian_sheaf_smallGrothendieckTopology`.

## Main declarations

- `CategoryTheory.HasSmallSiteSheafify.of_concreteCategory`: a concrete category over
  `Type (u + 1)` with a well-behaved forgetful functor has small-site sheafification.

-/

@[expose] public section

universe u' u

namespace CategoryTheory

open Limits

/-- A category concrete over `Type (u + 1)` whose forgetful functor preserves limits and
filtered colimits of size `u + 1` and reflects isomorphisms has small-site sheafification:
Mathlib's plus-construction provides a left exact sheafification on every `u + 1`-small
site. -/
instance (priority := low) HasSmallSiteSheafify.of_concreteCategory (A : Type u')
    [Category.{u + 1} A] {FA : A → A → Type*} {CA : A → Type (u + 1)}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
    [HasLimitsOfSize.{u + 1, u + 1} A] [HasColimitsOfSize.{u + 1, u + 1} A]
    [PreservesLimitsOfSize.{u + 1, u + 1} (forget A)] [(forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (forget A)] :
    HasSmallSiteSheafify A where
  hasSheafify _ := inferInstance

variable (Λ : Type (u + 1)) [Ring Λ]

example : HasSmallSiteSheafify (ModuleCat.{u + 1} Λ) := inferInstance

example : HasSmallSiteSheafify AddCommGrpCat.{u + 1} := inferInstance

end CategoryTheory
