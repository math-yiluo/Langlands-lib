/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardUniversalSingleRankMatch
public import WeilConjectures.AlgebraicGeometry.PicardUniversalRankMatch
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank

/-! # Rank of tensor pullbacks along composites

Tensor pullback preserves finite local freeness of a fixed rank, also along
composites. The common-neighbourhood rank condition itself is
`picardUniversalRankMatch_of_singleRankMatch_without_unit`.

Source: Stacks Project, Tag 0BDP, rank decomposition and the two rank-r loci.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private noncomputable def tensorIso {A B : Scheme.{u}} (a : A ⟶ B) :
    Modules.tensorPullback a ≅ Modules.pullback a :=
  (Classical.choice (Modules.nonempty_tensorPullbackAdjunction a)).leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction a)

/-- Tensor pullback preserves finite local freeness of a fixed rank. -/
theorem Modules.isFiniteLocallyFreeOfRank_tensorPullback {A B : Scheme.{u}} (a : A ⟶ B)
    (M : B.Modules) (r : ℕ)
    (hr : M.IsFiniteLocallyFreeOfRank r) :
    ((Modules.tensorPullback a).obj M).IsFiniteLocallyFreeOfRank r := by
  let := hr
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso ((tensorIso a).app M).symm

/-- Tensor pullback along a composite preserves finite local freeness of a fixed rank, given it
for the second map. -/
theorem Modules.isFiniteLocallyFreeOfRank_tensorPullback_comp {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C)
    (M : C.Modules) (r : ℕ)
    (hr : ((Modules.tensorPullback b).obj M).IsFiniteLocallyFreeOfRank r) :
    ((Modules.tensorPullback (a ≫ b)).obj M).IsFiniteLocallyFreeOfRank r := by
  have hr' : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Modules.tensorPullback b ⋙ Modules.tensorPullback a).obj M) r :=
    Modules.isFiniteLocallyFreeOfRank_tensorPullback a _ r hr
  let := hr'
  obtain ⟨e⟩ := Modules.nonempty_tensorPullbackComp a b
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (e.app M).symm

end AlgebraicGeometry.Scheme
