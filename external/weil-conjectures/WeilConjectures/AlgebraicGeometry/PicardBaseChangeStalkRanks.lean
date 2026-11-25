/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardUniversalRankMatch
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.PicardBaseChangeStalkFiniteBases
import WeilConjectures.AlgebraicGeometry.PicardBaseChangeStalkFinrankEq

/-! # Equal finite ranks of the stalks in Picard base change

Source: Stacks Project, Tags 0BDP and 01C6.
(blueprint: lem-sc-picard-base-change-stalk-ranks).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The two modules in a Picard base-change map have finite, isomorphic stalks.
This compares the objects only; it makes no assertion about the canonical map.
Source: Stacks Project, Tag 0BDP, common-rank reduction in the first three proof
paragraphs; Tag 01C6, finite locally free modules and their ranks.
(blueprint: lem-sc-picard-base-change-stalk-ranks)

Proof:
1. Apply hR to the identity of T at h(t). On the resulting neighbourhood V, both
   ordinary direct images are free locally of a common finite rank r, and E has rank r
   on X_V. The dual of a local rank-r frame is another rank-r frame.
   Pulling either direct image back to T' preserves these local frames. Thus
   the source stalk is a finite free O_{T',t}-module of rank r.
2. Apply hR to h at t to get a neighbourhood W and a rank s for the direct images
   over T'. The canonical associativity isomorphism of the two pullback squares and
   the tensor-pullback composition isomorphism identify the target with the appropriate
   direct image for h composed with g. Its stalk is free of rank s.
3. If the fibre of X_T over h(t) is nonempty, lift a point of that fibre after extending
   its residue field to a common extension with kappa(t). At this point of X_{T'},
   the pulled-back E has rank both r and s, by steps 1 and 2. Invariant basis number
   over its nonzero local ring gives r = s. This does not require connected fibres.
   If that fibre is empty, properness makes its complement in the image an open
   neighbourhood of h(t). Both direct images vanish there, before and after h, so
   both stalks are zero. This also handles rank zero.
4. Choose local frames and identify each stalk with O_{T',t}^r. Compose one frame with
   the inverse of the other to obtain the linear equivalence. The target is finitely
   generated because it is finite free. These choices are only witnesses in a theorem,
   not data of a definition. There is no point to check when T' is empty. -/
theorem picardRankMatch_baseChange_stalk_ranks {X S T : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree] (g : T ⟶ S)
    (hR : PicardUniversalRankMatch f E g) {T' : Scheme.{u}} (h : T' ⟶ T)
    (F : X.Modules) (hF : F = E ∨ F = Modules.dual E) (t : T') :
    let P := (Modules.tensorPullback h).obj
      ((Modules.pushforward (pullback.snd f g)).obj
        ((Modules.tensorPullback (pullback.fst f g)).obj F))
    let Q := (Modules.pushforward (pullback.snd (pullback.snd f g) h)).obj
      ((Modules.tensorPullback (pullback.fst (pullback.snd f g) h)).obj
        ((Modules.tensorPullback (pullback.fst f g)).obj F))
    Module.Finite (T'.presheaf.stalk t) (Q.presheaf.stalk t) ∧
      Nonempty (P.presheaf.stalk t ≃ₗ[T'.presheaf.stalk t] Q.presheaf.stalk t) := by
  obtain ⟨⟨r, ⟨bP⟩⟩, ⟨s, ⟨bQ⟩⟩⟩ :=
    picardRankMatch_baseChange_stalk_finite_bases f E g hR h F hF t
  have hrs : r = s := by
    have he := picardRankMatch_baseChange_stalk_finrank_eq f E g hR h F hF t
    simpa only [Module.finrank_eq_card_basis bP, Module.finrank_eq_card_basis bQ,
      Fintype.card_fin] using he
  subst s
  exact ⟨Module.Finite.of_basis bQ, ⟨bP.equiv bQ (Equiv.refl _)⟩⟩

end AlgebraicGeometry.Scheme
