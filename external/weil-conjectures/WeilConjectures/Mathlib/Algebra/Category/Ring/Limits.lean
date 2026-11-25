/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.Ring.Limits

/-!

# The forgetful functor from rings to abelian groups preserves limits of all sizes

Mathlib's `RingCat.forget₂AddCommGroup_preservesLimitsOfSize` preserves limits of diagrams
whose objects and morphisms live in the same universe. This file records that it preserves
limits of all sizes small enough, so that in particular it preserves sheaves on a site whose
objects and morphisms live in different universes (`GrothendieckTopology.HasSheafCompose`).

-/

@[expose] public section

universe v w u

open CategoryTheory Limits

/-- The forgetful functor from rings to abelian groups preserves all limits of size at most the
universe of the rings. -/
instance RingCat.forget₂AddCommGroup_preservesLimitsOfSize' [UnivLE.{v, u}] [UnivLE.{w, u}] :
    PreservesLimitsOfSize.{v, w} (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  preservesLimitsOfSize_of_univLE.{u, u, v, w} _
