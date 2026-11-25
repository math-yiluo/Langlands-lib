/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Limits.HasLimits


public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!

# Colimits of size `u` from colimits of size `u + 1`

The coefficient categories of this development have `Hom`-types in the universe `u + 1`,
one above the universe `u` of the base schemes, and a Grothendieck abelian such category
has colimits of size `u + 1` by `CategoryTheory.IsGrothendieckAbelian.hasColimits`. The
colimits indexed by the small sites are of size `u`, so they have to be obtained by
shrinking. Mathlib's `CategoryTheory.Limits.hasColimitsOfSizeShrink` does exactly this,
but is deliberately not an instance: in that generality instance search would climb the
universes without terminating.

This file registers the single consequence of it that the development needs, so that
`HasColimitsOfSize.{u, u} A` need not be carried as a hypothesis alongside
`IsGrothendieckAbelian.{u + 1} A`.

The same shrinking is needed for the *exactness* of these colimits: a Grothendieck abelian
category `IsGrothendieckAbelian.{w} A` satisfies `AB5OfSize.{w, w}` by definition, and
`CategoryTheory.AB5OfSize_of_univLE` brings this down to filtered colimits of size `0`.
The instance `CategoryTheory.Limits.hasExactColimitsOfShape_int` records the case of the
filtered shape `ℤ`, which is what the K-flat left derivability structure asks for.

-/

@[expose] public section

universe w v u' u

namespace CategoryTheory.Limits

/-- A category with `Hom`-types in `u + 1` and colimits of size `u + 1` has colimits of
size `u`, by `hasColimitsOfSizeShrink`.

Instance search does not climb the universes here: discharging the hypothesis
`HasColimitsOfSize.{u + 1, u + 1} A` through this very instance would require
`Category.{u + 2} A`, which the `Category.{u + 1} A` binder rules out. -/
instance hasColimitsOfSize_of_succ_grothendieck (A : Type u') [Category.{u + 1} A]
    [HasColimitsOfSize.{u + 1, u + 1} A] : HasColimitsOfSize.{u, u} A :=
  hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} A

/-- A Grothendieck abelian category has exact `ℤ`-indexed colimits: it satisfies
`AB5OfSize.{w, w}`, hence `AB5OfSize.{0, 0}` by `CategoryTheory.AB5OfSize_of_univLE` and
`UnivLE.{0, w}`, and `ℤ` is a filtered category of that size. -/
instance hasExactColimitsOfShape_int (A : Type u') [Category.{v} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasColimitsOfShape ℤ A] : HasExactColimitsOfShape ℤ A :=
  have := AB5OfSize_of_univLE.{0, 0, w, w} A
  inferInstance

end CategoryTheory.Limits
