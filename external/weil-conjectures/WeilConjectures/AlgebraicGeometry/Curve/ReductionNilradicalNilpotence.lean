/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Noetherian.Nilpotent

/-! # A uniform nilpotence exponent for a Noetherian scheme

Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1.
(blueprint: lem-sc-reduction-nilradical-nilpotent)
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- A positive power of the nilradical ideal sheaf of a Noetherian scheme is zero.
Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1.
(blueprint: lem-sc-reduction-nilradical-nilpotent)

Proof: Each point has an affine neighbourhood whose section ring is Noetherian.
The ring nilradical is nilpotent. Compactness selects finitely many of these
neighbourhoods. One more than the maximum of their exponents kills the nilradical
on every member of the cover; equality of ideal sheaves is tested on that cover.
The empty scheme is included: the empty maximum is zero. -/
theorem exists_nilradical_pow_succ_eq_bot (X : Scheme.{u}) [IsNoetherian X] :
    ∃ n : ℕ, X.nilradical ^ (n + 1) = ⊥ := by
  have key (x : X) : ∃ (V : X.affineOpens) (N : ℕ), x ∈ V.1 ∧
      X.nilradical.ideal V ^ N = ⊥ := by
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
    have := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    obtain ⟨N, hN⟩ := IsNoetherianRing.isNilpotent_nilradical Γ(X, V)
    refine ⟨⟨V, hV⟩, N, hxV, ?_⟩
    exact hN
  choose V N hxV hN using key
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (V x).1 : X → Set X)
    (fun x ↦ (V x).1.isOpen) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxV x⟩)
  refine ⟨t.sup N, IdealSheafData.ext_of_iSup_eq_top (fun x : t ↦ V x) ?_ ?_⟩
  · apply top_le_iff.mp
    intro x hx
    obtain ⟨y, hyt, hxy⟩ : ∃ y ∈ t, x ∈ (V y).1 := by simpa using ht (Set.mem_univ x)
    exact Opens.mem_iSup.mpr ⟨⟨y, hyt⟩, hxy⟩
  · intro x
    simp only [IdealSheafData.ideal_pow, Pi.pow_apply, IdealSheafData.ideal_bot,
      Pi.bot_apply]
    apply le_bot_iff.mp
    exact (Ideal.pow_le_pow_right
      ((Finset.le_sup x.2).trans (Nat.le_succ _))).trans (hN x).le

end AlgebraicGeometry.Scheme
