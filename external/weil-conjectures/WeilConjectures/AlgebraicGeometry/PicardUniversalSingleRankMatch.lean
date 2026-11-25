/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # One direct-image rank condition with a reference bundle

Source: Stacks Project, Tag 0BDP, first three proof paragraphs.
(blueprint: def-sc-picard-universal-single-rank-match).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The universal local rank of the direct image of F agrees with the rank of E.
The reference E fixes the rank on the whole inverse image of each neighbourhood.
This is one of the two direct-image clauses used in Tag 0BDP, with F equal to E
or its dual; no condition on the other direct image is imposed.
Source: Stacks Project, Tag 0BDP, first three proof paragraphs.
(blueprint: def-sc-picard-universal-single-rank-match). -/
def PicardUniversalSingleRankMatch {X S T : Scheme.{u}} (f : X ⟶ S)
    (E F : X.Modules) (g : T ⟶ S) : Prop :=
  ∀ {T' : Scheme.{u}} (h : T' ⟶ T) (t : T'),
    ∃ U : T'.Opens, t ∈ U ∧ ∃ r : ℕ,
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback U.ι).obj
          ((Modules.pushforward (pullback.snd f (h ≫ g))).obj
            ((Modules.tensorPullback (pullback.fst f (h ≫ g))).obj F))) r ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback (pullback.fst f (U.ι ≫ h ≫ g))).obj E) r

end AlgebraicGeometry.Scheme
