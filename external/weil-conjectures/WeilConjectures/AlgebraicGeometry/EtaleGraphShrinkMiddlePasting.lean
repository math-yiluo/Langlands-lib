/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphNeighborhoodWords
import WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkFirstLeg
import WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkSecondLeg

/-! # Intersection pasting for a shrinking graph neighborhood

Source: Stacks Project, Tag 0F7J, graph neighborhood pasting
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar openImmersionLowerShriek rightDerivedLowerStarComp

/-- The intersection word absorbs the inverse triangle from a smaller neighborhood.
Source: Stacks Tag 0F7J, product-graph extension, intersection calculation
(auxiliary; not a blueprint node).

Proof: the ambient product and first graph neighborhood do not change. Pull the open
map of second neighborhoods back to their intersections with the first neighborhood.
Both proper graph lifts factor through this pulled-back open, since both projections
agree by graphNeighborhoodShrink_graph. Apply horizontal exchange pasting first to
the intersection triangle and the projection to the first neighborhood, and then to
the same triangle and the projection to the second neighborhood. The two occurrences
of the smaller intersection triangle have opposite orientations and cancel. Open
composition associativity identifies the remaining open word with the specified
neighborhood triangle. Whisker by the common ambient proper direct image and insert
the functor associators. This gives exactly the two displayed middle words; no side
comparison or final graph comparison is assumed. -/
theorem etaleGraphShrinkMiddlePasting
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z W : Scheme.{u}} {h : X ⟶ Z} (c : Compactification h)
    (H : EtaleGraphPresentation h) (a' : X ⟶ W) (v : W ⟶ H.U)
    [IsProper a'] [IsOpenImmersion v] (fac : a' ≫ v = H.a) :
    (H.graphMiddle c A).hom ≫ (H.graphNeighborhoodTriangle c A a' v fac).hom =
      (H.graphFirstShrinkIso c A a' v fac).hom ≫
        ((H.shrink a' v fac).graphMiddle c A).hom  := by
  rw [H.graphMiddle_eq_intersectionLegs c A,
    (H.shrink a' v fac).graphMiddle_eq_intersectionLegs c A]
  rw [Category.assoc, etaleGraphShrinkSecondLeg A c H a' v fac,
    ← Category.assoc, etaleGraphShrinkFirstLeg A c H a' v fac,
    Category.assoc]

end AlgebraicGeometry.Etale
