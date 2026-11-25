/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic

/-!
# Exact filtered colimits of size `(u, u + 1)` in a Grothendieck abelian category

The coefficient categories of this development have `Hom`-types in the universe `u + 1`,
one above the universe `u` of the base schemes, and are Grothendieck abelian relative to
`u + 1`, so they have exact filtered colimits of size `(u + 1, u + 1)`. The filtered
colimits that occur are indexed by categories with objects in `Type (u + 1)` and
`Hom`-types in `Type u`. This file registers the resulting instances
`CategoryTheory.IsGrothendieckAbelian.hasFilteredColimitsOfSize_of_succ` and
`CategoryTheory.IsGrothendieckAbelian.ab5OfSize_of_succ` at that size, so that they need
not be carried as hypotheses alongside `IsGrothendieckAbelian.{u + 1} A`.

It also records that coproducts indexed by a `w`-small type exist and are exact in a
Grothendieck abelian category relative to `w`
(`CategoryTheory.IsGrothendieckAbelian.hasColimitsOfShape_discrete`,
`CategoryTheory.IsGrothendieckAbelian.hasExactColimitsOfShape_discrete`), e.g. those indexed
by `ℤ`.
-/

@[expose] public section

universe u' u

namespace CategoryTheory.IsGrothendieckAbelian

open Limits

/-- A Grothendieck abelian category with `Hom`-types in `u + 1` has filtered colimits of
size `(u, u + 1)`.

Instance search does not climb the universes here: discharging the hypothesis
`IsGrothendieckAbelian.{u + 1} A` through this very instance would require
`Category.{u + 2} A`, which the `Category.{u + 1} A` binder rules out. -/
instance hasFilteredColimitsOfSize_of_succ (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] : HasFilteredColimitsOfSize.{u, u + 1} A :=
  hasFilteredColimitsOfSize_of_univLE.{u, u + 1, u + 1, u + 1}

/-- A Grothendieck abelian category with `Hom`-types in `u + 1` has *exact* filtered
colimits of size `(u, u + 1)`. -/
instance ab5OfSize_of_succ (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] : AB5OfSize.{u, u + 1} A :=
  AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} A

section Discrete

universe w v w'

variable (C : Type u') [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  (J : Type w') [Small.{w} J]

/-- A Grothendieck abelian category relative to `w` has coproducts indexed by `w`-small
types. -/
lemma hasColimitsOfShape_discrete : HasColimitsOfShape (Discrete J) C :=
  hasColimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink.{w} J).symm)

/-- In a Grothendieck abelian category relative to `w`, coproducts indexed by `w`-small types
are exact (`AB4`). -/
lemma hasExactColimitsOfShape_discrete :
    haveI := hasColimitsOfShape_discrete C J
    HasExactColimitsOfShape (Discrete J) C :=
  HasExactColimitsOfShape.of_domain_equivalence C
    (Discrete.equivalence (equivShrink.{w} J).symm)

end Discrete

end CategoryTheory.IsGrothendieckAbelian
