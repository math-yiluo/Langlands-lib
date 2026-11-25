/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Grothendieck abelian categories of modules over a commutative ring

A shortcut instance: `ModuleCat R` is Grothendieck abelian for a commutative ring `R`.

## Implementation notes

The Mathlib instance is stated for a `Ring R`, so for a commutative ring the instance proof
found by type class search is `instIsGrothendieckAbelianModuleCat R (CommRing.toRing R)`. Its
argument is not atomic, so the elaborator abstracts every occurrence of this proof inside a
definition into an auxiliary lemma. For the derived tensor product of étale sheaves of
`R`-modules, the kernel then fails to compare the auxiliary lemma with the original proof in
reasonable time (a deterministic timeout). The shortcut takes the `CommRing` instance itself
as argument, so the proof stays atomic and is not abstracted.
-/

@[expose] public section

universe u

open CategoryTheory

-- TODO: remove this shortcut once the Mathlib instance no longer has its proof abstracted
-- into an auxiliary lemma inside definitions involving the derived tensor product.
/-- `ModuleCat R` is Grothendieck abelian for a commutative ring `R`: a shortcut for the
Mathlib instance, whose proof term stays atomic (see the implementation notes). -/
instance (priority := high) ModuleCat.isGrothendieckAbelian_of_commRing (R : Type u)
    [CommRing R] : IsGrothendieckAbelian.{u} (ModuleCat.{u} R) :=
  inferInstance
