/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardCupProductMap
import WeilConjectures.AlgebraicGeometry.PicardCounitEqualRanks
import WeilConjectures.AlgebraicGeometry.PicardCupProductSplitCounit
import WeilConjectures.AlgebraicGeometry.PicardCupProductOfCounit
import WeilConjectures.AlgebraicGeometry.PicardPullbackPerfectPairing

/-! # The local dual-basis criterion for degree-zero cup product

Source: Stacks Project, Tag 0BDP, final paragraph.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- On a single base, cup product detects the evaluation counit when the direct image
and the bundle have the same local rank. Neither properness nor flatness nor universal
base-change compatibility is an assumption of this local calculation.

Source: Stacks Project, Tag 0BDP, final paragraph, the two displayed dual bases.
(blueprint: lem-sc-picard-cup-product-local-dual-bases)

Proof: Put p = X_W → W, q = X_W → X, M = q^*E and N = p_*M.
If the cup transpose is invertible, the pushed pairing is perfect. Since N is
finite locally free, pulling this exact pairing back and using the proved cup
counit identity gives a retraction of p^*N → M. On each neighbourhood supplied
by hRanks, this is a split injection between locally free modules of rank r.
At stalks a split injection between finite free modules of equal rank is bijective;
stalk detection and the open cover therefore make the counit invertible.
Conversely the explicit evaluation pairing between q^*E and q^*(dual E) is perfect:
monoidal pullback preserves the exact pairing, and the canonical unit comparison
differs from the monoidal one by a scalar automorphism. If the counit is invertible,
for every W-module P the adjunction, perfect evaluation, tensor comparison and
invertible structure-sheaf unit identify Hom(P,p_*q^*(dual E)) with Hom(P,dual N).
Naturality and the cup counit identity identify this bijection with postcomposition
by the cup transpose. Yoneda proves that transpose invertible. Rank zero and empty
schemes are included in these categorical and stalkwise arguments. -/
theorem picardCupProduct_isIso_iff_counit_of_local_ranks
    {X S W : Scheme.{u}} (f : X ⟶ S) (E : X.Modules) [E.IsFiniteLocallyFree]
    (j : W ⟶ S)
    (hO : IsIso ((Classical.choose
      (Modules.exists_tensorPullbackAdjunction (pullback.snd f j))).unit.app
        (SheafOfModules.unit W.ringCatSheaf)))
    (hN : ((Modules.pushforward (pullback.snd f j)).obj
      ((Modules.tensorPullback (pullback.fst f j)).obj E)).IsFiniteLocallyFree)
    (hRanks : ∀ w : W, ∃ U : W.Opens, w ∈ U ∧ ∃ r : ℕ,
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback U.ι).obj
          ((Modules.pushforward (pullback.snd f j)).obj
            ((Modules.tensorPullback (pullback.fst f j)).obj E))) r ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback (pullback.fst f (U.ι ≫ j))).obj E) r) :
    IsIso (picardCupProductMap f E j hO) ↔
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f j))).counit.app
          ((Modules.tensorPullback (pullback.fst f j)).obj E)) := by
  let p := pullback.snd f j
  let q := pullback.fst f j
  let M := (Modules.tensorPullback q).obj E
  let D := (Modules.tensorPullback q).obj (Modules.dual E)
  let ev : MonoidalCategoryStruct.tensorObj M D ⟶ SheafOfModules.unit (pullback f j).ringCatSheaf :=
    (Modules.picardTensorObjIso q E (Modules.dual E)).inv ≫
      (Modules.tensorPullback q).map (Modules.dualEvaluation E) ≫
        (Modules.picardTensorUnitIso q).hom
  let adj := Classical.choose (Modules.exists_tensorPullbackAdjunction p)
  change IsIso (MonoidalClosed.curry (Modules.picardPushforwardPairing p hO M D ev)) ↔
    IsIso (adj.counit.app M)
  constructor
  · intro h
    have : ((Modules.pushforward p).obj M).IsFiniteLocallyFree := hN
    have : IsSplitMono (adj.counit.app M) :=
      Modules.isSplitMono_counit_of_isIso_picardPushforwardPairing p hO M D ev h
    exact isIso_of_isSplitMono_of_picard_local_ranks f E j
      ((Modules.pushforward p).obj M) hRanks (adj.counit.app M)
  · intro h
    exact Modules.isIso_curry_picardPushforwardPairing_of_isIso_counit p hO M D ev
      (Modules.isIso_curry_picardPullbackEvaluation q E) h

end AlgebraicGeometry.Scheme
