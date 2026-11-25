/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Grothendieck topoi with a small-site presentation

Source: Stacks Project, Sites, Tags 00XA, 00Z4, 00Z8 and 00VI
(blueprint: def-weil-pbc-topos).

Sieves, their pullbacks, Grothendieck topologies and sheaves are the existing Mathlib notions.
The universe `w` represents the larger universe of the size convention
`prose-01-10`: both the presenting site and the values of its sheaves lie in it.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

/-- A category is a Grothendieck topos relative to universe `w` if it is equivalent to
`Type w`-valued sheaves on a site whose objects and morphisms belong to universe `w`.

The topology uses Mathlib's `Sieve` and its pullback, with the maximal-sieve, pullback-stability
and transitivity axioms of `GrothendieckTopology`. The category `Sheaf J (Type w)` is the full
subcategory of presheaves satisfying unique amalgamation for every covering sieve.

Source: Stacks Project, Sites, Tag 00XA (topoi), Tag 00Z4 (topologies), Tag 00Z8 (sheaves),
and Tag 00VI (small sites), with the universe convention `prose-01-10`
(blueprint: def-weil-pbc-topos). -/
def IsGrothendieckTopos (E : Type u) [Category.{v} E] : Prop :=
  ∃ (D : Type w) (c : SmallCategory D) (J : @GrothendieckTopology D c),
    Nonempty (E ≌ @Sheaf D c J (Type w) inferInstance)

end CategoryTheory
