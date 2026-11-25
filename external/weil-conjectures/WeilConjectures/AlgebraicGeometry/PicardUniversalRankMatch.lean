/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Universal rank matching for Picard direct images

Source: Stacks Project, Tag 0BDP (blueprint: def-sc-picard-universal-rank-match).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Universal local equality of the ranks of a module and its two ordinary direct images.
This is only the rank clause; it asserts no invertibility of canonical base-change maps.
Source: Stacks Project, Tag 0BDP, first three proof paragraphs.
(blueprint: def-sc-picard-universal-rank-match) -/
def PicardUniversalRankMatch {X S T : Scheme.{u}} (f : X ⟶ S)
    (E : X.Modules) (g : T ⟶ S) : Prop :=
  ∀ {T' : Scheme.{u}} (h : T' ⟶ T) (t : T'),
    ∃ U : T'.Opens, t ∈ U ∧ ∃ r : ℕ,
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback U.ι).obj
          ((Modules.pushforward (pullback.snd f (h ≫ g))).obj
            ((Modules.tensorPullback (pullback.fst f (h ≫ g))).obj E))) r ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback U.ι).obj
          ((Modules.pushforward (pullback.snd f (h ≫ g))).obj
            ((Modules.tensorPullback (pullback.fst f (h ≫ g))).obj
              (Modules.dual E)))) r ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback (pullback.fst f (U.ι ≫ h ≫ g))).obj E) r

end AlgebraicGeometry.Scheme
