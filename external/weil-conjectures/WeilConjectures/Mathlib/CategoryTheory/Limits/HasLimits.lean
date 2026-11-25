/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits

/-!

# Limits and colimits of small size from limits and colimits of size `u + 1`

The coefficient categories of this development have `Hom`-types in the universe `u + 1`, one
above the universe `u` of the base schemes, and a Grothendieck abelian such category has
limits and colimits of size `u + 1` by `CategoryTheory.IsGrothendieckAbelian.hasLimits` and
`CategoryTheory.IsGrothendieckAbelian.hasColimits`. The limits and colimits indexed by the
small sites — for instance the colimits computing a stalk, or the products entering the
skyscraper sheaf at a geometric point — are of size `u`, so they have to be obtained by
shrinking. Mathlib's `CategoryTheory.Limits.hasLimitsOfSizeShrink` and
`CategoryTheory.Limits.hasColimitsOfSizeShrink` do exactly this, but are deliberately not
instances: in that generality instance search would climb the universes without terminating.

The comma categories indexing a pointwise Kan extension along a functor between small
sites are one step less small: an object of such a comma category is an object of the site
together with a morphism, so it lives in `Type (u + 1)`, while the `Hom`-types are still
in `Type u`. So `HasColimitsOfSize.{u, u + 1} A` is needed as well.

This file registers the three consequences of the shrinking lemmas that the development
needs, so that `HasLimitsOfSize.{u, u} A`, `HasColimitsOfSize.{u, u} A` and
`HasColimitsOfSize.{u, u + 1} A` need not be carried as hypotheses alongside
`IsGrothendieckAbelian.{u + 1} A`.

-/

@[expose] public section

universe u' u

namespace CategoryTheory.Limits

/-- A category with `Hom`-types in `u + 1` and limits of size `u + 1` has limits of size
`u`, by `hasLimitsOfSizeShrink`.

Instance search does not climb the universes here: discharging the hypothesis
`HasLimitsOfSize.{u + 1, u + 1} A` through this very instance would require
`Category.{u + 2} A`, which the `Category.{u + 1} A` binder rules out. The priority is `low`
so that this attempt is made only after the instances which do provide limits of size
`u + 1`; tried first it aborts elaboration with a universe constraint error instead of
failing silently. -/
instance (priority := low) hasLimitsOfSize_of_succ (A : Type u') [Category.{u + 1} A]
    [HasLimitsOfSize.{u + 1, u + 1} A] : HasLimitsOfSize.{u, u} A :=
  hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} A

/-- A category with `Hom`-types in `u + 1` and colimits of size `u + 1` has colimits of
size `u`, by `hasColimitsOfSizeShrink`.

Instance search does not climb the universes here: discharging the hypothesis
`HasColimitsOfSize.{u + 1, u + 1} A` through this very instance would require
`Category.{u + 2} A`, which the `Category.{u + 1} A` binder rules out. As for
`hasLimitsOfSize_of_succ` the priority is `low`, so that the attempt is made only after the
instances which do provide colimits of size `u + 1`. -/
instance (priority := low) hasColimitsOfSize_of_succ (A : Type u') [Category.{u + 1} A]
    [HasColimitsOfSize.{u + 1, u + 1} A] : HasColimitsOfSize.{u, u} A :=
  hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} A

/-- A category with `Hom`-types in `u + 1` and colimits of size `u + 1` has colimits
indexed by categories with objects in `Type (u + 1)` and `Hom`-types in `Type u`, by
`hasColimitsOfSizeShrink`. Such are the comma categories indexing the pointwise left Kan
extensions along a functor between small sites.

Instance search does not climb the universes here: discharging the hypothesis
`HasColimitsOfSize.{u + 1, u + 1} A` through this very instance would require
`Category.{u + 2} A`, which the `Category.{u + 1} A` binder rules out. As for
`hasColimitsOfSize_of_succ` the priority is `low`, so that the attempt is made only after
the instances which do provide colimits of size `u + 1`. -/
instance (priority := low) hasColimitsOfSize_succ_of_succ (A : Type u') [Category.{u + 1} A]
    [HasColimitsOfSize.{u + 1, u + 1} A] : HasColimitsOfSize.{u, u + 1} A :=
  hasColimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} A

end CategoryTheory.Limits

namespace CategoryTheory.Limits

/-- **Universal property of the chosen colimit.** For a diagram `F : J ⥤ C` having a colimit,
with coprojections `colimit.ι F j`, every cocone `s` on `F` receives exactly one morphism
`colimit F ⟶ s.pt` compatible with the coprojections, namely `colimit.desc F s`.
(blueprint: `def-weil-pbc-category-colimit`) -/
theorem colimit.existsUnique_desc {J : Type*} [Category* J] {C : Type*} [Category* C]
    (F : J ⥤ C) [HasColimit F] (s : Cocone F) :
    ∃! u : colimit F ⟶ s.pt, ∀ j, colimit.ι F j ≫ u = s.ι.app j :=
  ⟨colimit.desc F s, fun j ↦ colimit.ι_desc s j,
    fun u hu ↦ colimit.hom_ext fun j ↦ by simp [hu]⟩

end CategoryTheory.Limits
