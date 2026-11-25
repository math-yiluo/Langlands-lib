/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardUniversalSingleRankMatch
public import WeilConjectures.AlgebraicGeometry.PicardUniversalRankMatch
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
import WeilConjectures.AlgebraicGeometry.Modules.LocalDerivation
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Synchronizing rank witnesses, including empty fibres

Source: Stacks Project, Tag 0BDP, the intersection of the two rank loci;
the empty-fibre case is the adaptation in the parent rank-match construction.
(blueprint: lem-sc-picard-universal-rank-match-synchronization).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Fixed rank persists on a smaller open neighbourhood. -/
private theorem shrink_rank {A : Scheme.{u}} (M : A.Modules) (U W : A.Opens)
    (hWU : W ≤ U) (r : ℕ)
    (hr : ((Modules.tensorPullback U.ι).obj M).IsFiniteLocallyFreeOfRank r) :
    ((Modules.tensorPullback W.ι).obj M).IsFiniteLocallyFreeOfRank r := by
  let a := A.homOfLE hWU
  have := hr
  let comparison := (Modules.nonempty_tensorPullbackAdjunction a).some.leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction a)
  let e := comparison.symm.app ((Modules.tensorPullback U.ι).obj M) ≪≫
    (Modules.nonempty_tensorPullbackComp a U.ι).some.symm.app M ≪≫
      eqToIso (congrArg (fun k ↦ (Modules.tensorPullback k).obj M) (A.homOfLE_ι hWU))
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e

/-- Restrict the reference rank using the canonical map of fibre products. -/
private theorem shrink_reference_rank {X S T : Scheme.{u}} (f : X ⟶ S)
    (E : X.Modules) (g : T ⟶ S) (U W : T.Opens) (hWU : W ≤ U) (r : ℕ)
    (hr : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Modules.tensorPullback (pullback.fst f (U.ι ≫ g))).obj E) r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Modules.tensorPullback (pullback.fst f (W.ι ≫ g))).obj E) r := by
  let a := pullback.map f (W.ι ≫ g) f (U.ι ≫ g)
    (𝟙 X) (T.homOfLE hWU) (𝟙 S) (by simp)
    (by simp [← Category.assoc, T.homOfLE_ι hWU])
  have := hr
  let comparison := (Modules.nonempty_tensorPullbackAdjunction a).some.leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction a)
  let e := comparison.symm.app ((Modules.tensorPullback (pullback.fst f (U.ι ≫ g))).obj E) ≪≫
    (Modules.nonempty_tensorPullbackComp a (pullback.fst f (U.ι ≫ g))).some.symm.app E
  have ha : a ≫ pullback.fst f (U.ι ≫ g) = pullback.fst f (W.ι ≫ g) := by
    simp [a]
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
    (e ≪≫ eqToIso (congrArg (fun k ↦ (Modules.tensorPullback k).obj E) ha))

/-- An ordinary direct image restricted over an empty inverse image has rank zero. -/
private theorem rank_zero_of_empty_preimage {A B : Scheme.{u}} (f : A ⟶ B)
    (M : A.Modules) (U : B.Opens) (he : f ⁻¹ᵁ U = ⊥) (r : ℕ)
    (hr : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Modules.tensorPullback U.ι).obj ((Modules.pushforward f).obj M)) r)
    (t : U.toScheme) : r = 0 := by
  let N := ((Modules.pushforward f).obj M).restrict U.ι
  have : N.IsFiniteLocallyFreeOfRank r := by
    have := hr
    let e := (Modules.nonempty_tensorPullbackAdjunction U.ι).some.leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction U.ι)
    exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      (e.app _ ≪≫ (Modules.restrictFunctorIsoPullback U.ι).symm.app _)
  obtain ⟨V, hV, htV, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := U.toScheme) (x := t) (U := ⊤) trivial
  obtain ⟨p, hp⟩ := hV.range_fromSpec.ge htV
  have hbot : f ⁻¹ᵁ (U.ι ''ᵁ V) = ⊥ := by
    apply le_antisymm _ bot_le
    rw [← he]
    exact f.preimage_mono (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact y.2)
  have hs : Subsingleton Γ(N, V) := by
    let e := Modules.restrictAppIso U.ι ((Modules.pushforward f).obj M) V
    have hsub : Subsingleton Γ((Modules.pushforward f).obj M, U.ι ''ᵁ V) := by
      change Subsingleton Γ(M, f ⁻¹ᵁ (U.ι ''ᵁ V))
      rw [hbot]
      exact Modules.subsingleton_sections_bot M
    exact ⟨fun a b ↦ (ConcreteCategory.bijective_of_isIso e.hom).1
      (Subsingleton.elim _ _)⟩
  have := hs
  have hh := Modules.rankAtStalk_sections_eq N (r := r) hV p
  rw [Module.rankAtStalk_eq_zero_of_subsingleton] at hh
  exact hh.symm

/-- The two single-image conditions have a common local rank witness even on empty fibres.
Source: Stacks Project, Tag 0BDP, first and third proof paragraphs, and the
empty-fibre rank-zero clause of the parent construction.
(blueprint: lem-sc-picard-universal-rank-match-synchronization)

Proof: Fix a further base change h and a point t. Choose U containing t with rank r
from the E direct-image condition, and V containing t with rank s from the dual
condition. Let W=U intersect V. Tensor pullback composition and the canonical
isomorphisms of iterated fibre products identify the restrictions of the two
reference bundles with the same E on X_W. Restriction preserves fixed-rank finite
local freeness, so E on X_W has both ranks r and s.

If X_W has a point, compute the rank at its nonzero local-ring stalk: invariant
basis number gives r=s. If X_W has no points, it is the empty scheme. Restriction
of an ordinary pushforward to an open equals the pushforward from its inverse
image, so both direct images restricted to W are zero. Since W contains t, its
local-ring stalk at t is nonzero; the first zero direct image has rank r only if
r=0, and the second has rank s only if s=0. Thus again r=s. The two restricted
direct images and E on X_W therefore all have rank r, giving the common W witness.
This works for every h and t. Empty test schemes have no t to check. No
structure-sheaf unit or nonempty-fibre assumption is used.
-/
theorem picardUniversalRankMatch_of_singleRankMatch_without_unit
    {X S T : Scheme.{u}} (f : X ⟶ S) (E : X.Modules) (g : T ⟶ S)
    (hE : PicardUniversalSingleRankMatch f E E g)
    (hdual : PicardUniversalSingleRankMatch f E (Modules.dual E) g) :
    PicardUniversalRankMatch f E g := by
  classical
  intro T' h t
  obtain ⟨U, htU, r, hrN, hrE⟩ := hE h t
  obtain ⟨V, htV, s, hsN, hsE⟩ := hdual h t
  let W : T'.Opens := U ⊓ V
  have hrN' := shrink_rank _ U W inf_le_left r hrN
  have hsN' := shrink_rank _ V W inf_le_right s hsN
  have hrE' := shrink_reference_rank f E (h ≫ g) U W inf_le_left r hrE
  have hsE' := shrink_reference_rank f E (h ≫ g) V W inf_le_right s hsE
  have hrs : r = s := by
    by_cases hne : Nonempty (pullback f (W.ι ≫ h ≫ g) : Scheme.{u})
    · obtain ⟨x⟩ := hne
      have := hrE'
      have h₁ := Modules.finiteLocallyFreeOfRank_stalk_finrank
        ((Modules.tensorPullback (pullback.fst f (W.ι ≫ h ≫ g))).obj E) r x
      have := hsE'
      have h₂ := Modules.finiteLocallyFreeOfRank_stalk_finrank
        ((Modules.tensorPullback (pullback.fst f (W.ι ≫ h ≫ g))).obj E) s x
      exact h₁.symm.trans h₂
    · have : IsEmpty (pullback f (W.ι ≫ h ≫ g) : Scheme.{u}) :=
        not_nonempty_iff.mp hne
      let p := pullback.snd f (h ≫ g)
      let q := pullback.fst f (h ≫ g)
      have he : p ⁻¹ᵁ W = ⊥ := by
        apply le_antisymm _ bot_le
        intro x hx
        let a := pullback.map f (W.ι ≫ h ≫ g) f (h ≫ g)
          (𝟙 X) W.ι (𝟙 S) (by simp) (by simp)
        have hx' : x ∈ Set.range a := by
          change x ∈ Set.range (pullback.map f (W.ι ≫ h ≫ g) f (h ≫ g)
            (𝟙 X) W.ι (𝟙 S) (by simp) (by simp))
          rw [Pullback.range_map]
          exact ⟨⟨q x, rfl⟩, ⟨⟨p x, hx⟩, rfl⟩⟩
        obtain ⟨z, _⟩ := hx'
        exact isEmptyElim z
      have htW : t ∈ W := ⟨htU, htV⟩
      have hr0 := rank_zero_of_empty_preimage p
        ((Modules.tensorPullback q).obj E) W he r hrN' ⟨t, htW⟩
      have hs0 := rank_zero_of_empty_preimage p
        ((Modules.tensorPullback q).obj (Modules.dual E)) W he s hsN' ⟨t, htW⟩
      exact hr0.trans hs0.symm
  exact ⟨W, ⟨htU, htV⟩, r, hrN', hrs.symm ▸ hsN', hrE'⟩

end AlgebraicGeometry.Scheme
