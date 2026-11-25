/-
Adapted from the Anthropic Lean formalisation of Fermat's Last Theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, files
`Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth.lean`,
`Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupGenerator.lean`.
Copyright 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: the two files are merged; statements are on the Library's
`Langlands.Ramification.lowerGroup`; names follow the Library; the `ValuationSubring` wrappers, the
example blocks and the in-file checks are not kept; no options are set.
The paired Markdown file lists the changes.
-/

import Langlands.LocalFactor.Ramification.LowerGroup
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Topology.Order

/-!
# The depth of an automorphism of a discrete valuation ring

For a group acting on a discrete valuation ring `R` with additive valuation `v`, the depth
`ramificationDepth R G σ = ⨅ x, v (σ • x - x)` (Serre's `i_G(σ)`, with values in `ℕ∞`) measures how
far `σ` is from the identity: `σ ∈ lowerGroup R G i` exactly when `i + 1 ≤ ramificationDepth R G σ`.
When `R` is generated over a subring of invariants by one element `x`, the depth is `v (σ • x - x)`.
The file also proves that a faithful action of a finite group on a separated local ring has
trivial lower groups from some index on.
-/

namespace Langlands.Ramification

section

open scoped Pointwise

open IsLocalRing

section
open Subgroup

theorem exists_eq_bot_of_antitone_of_iInf_eq_bot {H : Type*} [Group H] [Finite H]
    {f : ℕ → Subgroup H} (hf : Antitone f) (hbot : ⨅ i, f i = ⊥) :
    ∃ N : ℕ, ∀ i, N ≤ i → f i = ⊥ := by
  classical
  cases nonempty_fintype H

  have key : ∀ g : H, ∃ n : ℕ, g ∈ f n → g = 1 := by
    intro g
    by_cases hg : g = 1
    · exact ⟨0, fun _ => hg⟩
    · have hnot : g ∉ ⨅ i, f i := by
        rw [hbot]
        simpa [Subgroup.mem_bot] using hg
      simp only [Subgroup.mem_iInf, not_forall] at hnot
      obtain ⟨n, hn⟩ := hnot
      exact ⟨n, fun h => absurd h hn⟩
  choose level hlevel using key
  refine ⟨Finset.univ.sup level, fun i hi => ?_⟩
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  exact hlevel g (hf (le_trans (Finset.le_sup (Finset.mem_univ g)) hi) hg)

end

section
open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

theorem smul_mem_maximalIdeal_pow_iff {σ : G} {n : ℕ} {x : R} :
    σ • x ∈ (maximalIdeal R) ^ n ↔ x ∈ (maximalIdeal R) ^ n := by
  have h := Ideal.smul_mem_pointwise_smul_iff (a := σ) (S := (maximalIdeal R) ^ n) (x := x)
  rwa [pointwise_smul_maximalIdeal_pow] at h

theorem exists_lowerGroup_eq_bot_of_iInf_eq_bot [Finite G] [FaithfulSMul G R]
    (hsep : ⨅ n, (maximalIdeal R) ^ n = ⊥) :
    ∃ N : ℕ, ∀ i, N ≤ i → lowerGroup R G i = ⊥ :=
  exists_eq_bot_of_antitone_of_iInf_eq_bot (lowerGroup_antitone _ _)
    (iInf_lowerGroup_eq_bot hsep)

theorem lowerGroup_finiteIndex [Finite G] (i : ℕ) :
    (lowerGroup R G i).FiniteIndex :=
  Subgroup.finiteIndex_of_finite

theorem isOpen_lowerGroup [TopologicalSpace G] [DiscreteTopology G] (i : ℕ) :
    IsOpen ((lowerGroup R G i : Subgroup G) : Set G) :=
  isOpen_discrete _

end

section
open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

theorem mem_maximalIdeal_pow_iff_le_addVal {n : ℕ} {x : R} :
    x ∈ (IsLocalRing.maximalIdeal R) ^ n ↔ (n : ℕ∞) ≤ addVal R x := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← addVal_le_iff_dvd, hϖ.addVal_pow]

theorem iInf_maximalIdeal_pow_eq_bot :
    ⨅ n : ℕ, (IsLocalRing.maximalIdeal R) ^ n = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_iInf] at hx
  rw [Ideal.mem_bot, ← addVal_eq_top_iff (R := R), ENat.eq_top_iff_forall_ge]
  intro m
  exact mem_maximalIdeal_pow_iff_le_addVal.mp (hx m)

theorem addVal_smul (σ : G) (x : R) : addVal R (σ • x) = addVal R x := by
  refine eq_of_forall_le_iff fun c => ?_
  induction c with
  | top => simp only [top_le_iff, addVal_eq_top_iff, smul_eq_zero_iff_eq]
  | coe n =>
    rw [← mem_maximalIdeal_pow_iff_le_addVal, ← mem_maximalIdeal_pow_iff_le_addVal,
      smul_mem_maximalIdeal_pow_iff]

variable (R G) in

noncomputable def ramificationDepth (σ : G) : ℕ∞ :=
  ⨅ x : R, addVal R (σ • x - x)

theorem ramificationDepth_def (σ : G) :
    ramificationDepth R G σ = ⨅ x : R, addVal R (σ • x - x) :=
  rfl

theorem le_ramificationDepth_iff {n : ℕ} {σ : G} :
    (n : ℕ∞) ≤ ramificationDepth R G σ ↔
      ∀ x : R, σ • x - x ∈ (IsLocalRing.maximalIdeal R) ^ n := by
  rw [ramificationDepth_def, le_iInf_iff]
  exact forall_congr' fun x => mem_maximalIdeal_pow_iff_le_addVal.symm

theorem mem_lowerGroup_iff_le_ramificationDepth {i : ℕ} {σ : G} :
    σ ∈ lowerGroup R G i ↔
      (i : ℕ∞) + 1 ≤ ramificationDepth R G σ := by
  rw [← Nat.cast_add_one, le_ramificationDepth_iff]
  exact mem_lowerGroup

theorem setOf_add_one_le_ramificationDepth_eq (i : ℕ) :
    {σ : G | (i : ℕ∞) + 1 ≤ ramificationDepth R G σ} =
      (lowerGroup R G i : Set G) := by
  ext σ
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe,
    mem_lowerGroup_iff_le_ramificationDepth]

theorem ramificationDepth_one : ramificationDepth R G (1 : G) = ⊤ := by
  rw [ramificationDepth_def]
  simp only [one_smul, sub_self, addVal_zero, iInf_top]

theorem ramificationDepth_eq_top_iff [FaithfulSMul G R] {σ : G} :
    ramificationDepth R G σ = ⊤ ↔ σ = 1 := by
  constructor
  · intro h
    refine FaithfulSMul.eq_of_smul_eq_smul (α := R) fun x => ?_
    have hle : ramificationDepth R G σ ≤ addVal R (σ • x - x) := by
      rw [ramificationDepth_def]
      exact iInf_le _ x
    rw [h, top_le_iff] at hle
    have hx : σ • x - x = 0 := addVal_eq_top_iff.mp hle
    rw [sub_eq_zero] at hx
    exact hx.trans (one_smul G x).symm
  · rintro rfl
    exact ramificationDepth_one

theorem exists_lowerGroup_eq_bot_of_isDiscreteValuationRing [Finite G] [FaithfulSMul G R] :
    ∃ N : ℕ, ∀ i, N ≤ i → lowerGroup R G i = ⊥ :=
  exists_lowerGroup_eq_bot_of_iInf_eq_bot iInf_maximalIdeal_pow_eq_bot

theorem isOpen_setOf_le_ramificationDepth [TopologicalSpace G] [DiscreteTopology G] (n : ℕ) :
    IsOpen {σ : G | (n : ℕ∞) ≤ ramificationDepth R G σ} :=
  isOpen_discrete _

end

end

section

open IsLocalRing

theorem sub_dvd_aeval_sub {A R : Type*} [CommSemiring A] [CommRing R] [Algebra A R]
    (x y : R) (p : Polynomial A) :
    x - y ∣ Polynomial.aeval x p - Polynomial.aeval y p := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, ← Polynomial.eval_map, ← Polynomial.eval_map]
  exact Polynomial.sub_dvd_eval_sub x y _

theorem sub_dvd_sub_of_mem_adjoin_singleton {A R : Type*} [CommSemiring A] [CommRing R]
    [Algebra A R] (σ : R →ₐ[A] R) {x r : R} (hr : r ∈ Algebra.adjoin A {x}) :
    σ x - x ∣ σ r - r := by
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hr
  obtain ⟨p, rfl⟩ := hr
  rw [← Polynomial.aeval_algHom_apply]
  exact sub_dvd_aeval_sub _ _ _

theorem sub_dvd_sub_of_adjoin_singleton_eq_top {A R : Type*} [CommSemiring A]
    [CommRing R] [Algebra A R] (σ : R →ₐ[A] R) {x : R} (hx : Algebra.adjoin A {x} = ⊤)
    (r : R) : σ x - x ∣ σ r - r :=
  sub_dvd_sub_of_mem_adjoin_singleton σ (by rw [hx]; exact Algebra.mem_top)

theorem smul_sub_dvd_smul_sub_of_mem_adjoin_singleton
    {A R : Type*} [CommSemiring A] [CommRing R] [Algebra A R]
    {G : Type*} [Monoid G] [MulSemiringAction G R] {σ : G}
    (hfix : ∀ a : A, σ • algebraMap A R a = algebraMap A R a)
    {x r : R} (hr : r ∈ Algebra.adjoin A {x}) :
    σ • x - x ∣ σ • r - r :=
  sub_dvd_sub_of_mem_adjoin_singleton
    { toFun := fun y => σ • y
      map_one' := smul_one σ
      map_mul' := fun y z => smul_mul' σ y z
      map_zero' := smul_zero σ
      map_add' := fun y z => smul_add σ y z
      commutes' := hfix } hr

theorem smul_sub_dvd_smul_sub_of_adjoin_singleton_eq_top
    {A R : Type*} [CommSemiring A] [CommRing R] [Algebra A R]
    {G : Type*} [Monoid G] [MulSemiringAction G R] {σ : G}
    (hfix : ∀ a : A, σ • algebraMap A R a = algebraMap A R a)
    {x : R} (hx : Algebra.adjoin A {x} = ⊤) (r : R) :
    σ • x - x ∣ σ • r - r :=
  smul_sub_dvd_smul_sub_of_mem_adjoin_singleton hfix
    (by rw [hx]; exact Algebra.mem_top)

section
open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]
variable {A : Type*} [CommSemiring A] [Algebra A R]

theorem addVal_smul_sub_le_of_adjoin_singleton_eq_top {σ : G}
    (hfix : ∀ a : A, σ • algebraMap A R a = algebraMap A R a)
    {x : R} (hx : Algebra.adjoin A {x} = ⊤) (r : R) :
    addVal R (σ • x - x) ≤ addVal R (σ • r - r) :=
  addVal_le_iff_dvd.mpr
    (smul_sub_dvd_smul_sub_of_adjoin_singleton_eq_top hfix hx r)

theorem ramificationDepth_eq_addVal_of_adjoin_singleton_eq_top {σ : G}
    (hfix : ∀ a : A, σ • algebraMap A R a = algebraMap A R a)
    {x : R} (hx : Algebra.adjoin A {x} = ⊤) :
    ramificationDepth R G σ = addVal R (σ • x - x) := by
  refine le_antisymm ?_ ?_
  · rw [ramificationDepth_def]
    exact iInf_le _ x
  · rw [ramificationDepth_def]
    exact le_iInf fun r => addVal_smul_sub_le_of_adjoin_singleton_eq_top hfix hx r

theorem mem_lowerGroup_iff_le_addVal_of_adjoin_singleton_eq_top {i : ℕ} {σ : G}
    (hfix : ∀ a : A, σ • algebraMap A R a = algebraMap A R a)
    {x : R} (hx : Algebra.adjoin A {x} = ⊤) :
    σ ∈ lowerGroup R G i ↔
      (i : ℕ∞) + 1 ≤ addVal R (σ • x - x) := by
  rw [mem_lowerGroup_iff_le_ramificationDepth,
    ramificationDepth_eq_addVal_of_adjoin_singleton_eq_top hfix hx]

theorem mem_lowerGroup_iff_smul_sub_mem_pow_of_adjoin_singleton_eq_top {i : ℕ}
    {σ : G} (hfix : ∀ a : A, σ • algebraMap A R a = algebraMap A R a)
    {x : R} (hx : Algebra.adjoin A {x} = ⊤) :
    σ ∈ lowerGroup R G i ↔
      σ • x - x ∈ (IsLocalRing.maximalIdeal R) ^ (i + 1) := by
  rw [mem_lowerGroup_iff_le_addVal_of_adjoin_singleton_eq_top hfix hx,
    mem_maximalIdeal_pow_iff_le_addVal, Nat.cast_add_one]

theorem addVal_smul_sub_eq_of_adjoin_singleton_eq_top {σ : G}
    (hfix : ∀ a : A, σ • algebraMap A R a = algebraMap A R a) {x y : R}
    (hx : Algebra.adjoin A {x} = ⊤) (hy : Algebra.adjoin A {y} = ⊤) :
    addVal R (σ • x - x) = addVal R (σ • y - y) :=
  (ramificationDepth_eq_addVal_of_adjoin_singleton_eq_top hfix hx).symm.trans
    (ramificationDepth_eq_addVal_of_adjoin_singleton_eq_top hfix hy)

theorem ramificationDepth_eq_addVal_of_smulCommClass [SMulCommClass G A R] (σ : G)
    {x : R} (hx : Algebra.adjoin A {x} = ⊤) :
    ramificationDepth R G σ = addVal R (σ • x - x) :=
  ramificationDepth_eq_addVal_of_adjoin_singleton_eq_top (fun a => smul_algebraMap σ a) hx

theorem mem_lowerGroup_iff_le_addVal_of_smulCommClass [SMulCommClass G A R]
    {i : ℕ} {σ : G} {x : R} (hx : Algebra.adjoin A {x} = ⊤) :
    σ ∈ lowerGroup R G i ↔
      (i : ℕ∞) + 1 ≤ addVal R (σ • x - x) :=
  mem_lowerGroup_iff_le_addVal_of_adjoin_singleton_eq_top
    (fun a => smul_algebraMap σ a) hx

end

end

end Langlands.Ramification
