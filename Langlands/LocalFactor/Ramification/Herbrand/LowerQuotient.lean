/-
Adapted from the Anthropic Lean formalisation of Fermat's Last Theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, files
`Theorems/Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.lean`,
`P2M/Sol/S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth.lean`,
`Theorems/Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top.lean`,
`P2M/Sol/S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_adjoin_singleton_eq_top.lean`,
`Theorems/Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField.lean`,
`P2M/Sol/S_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField.lean`,
`Theorems/Thm_IsDiscreteValuationRing_upperRamificationQuotientCompat_of_isSeparable_residueField.lean`,
`P2M/Sol/S_IsDiscreteValuationRing_upperRamificationQuotientCompat_of_isSeparable_residueField.lean`.
Copyright 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: the eight files (four statements and their proofs) are one module; the FLT proof name
spaces `P2MW.<file>.HerbrandPort.{FixedPoints, IsLocalRing, IsDiscreteValuationRing}` and
`P2MW.<file>.HerbrandPortE` are `Langlands.Ramification.LowerQuotient`; helper definitions and
lemmas that the FLT proofs carried twice are taken from `Herbrand/CosetDepth.lean`,
`Herbrand/RationalQuotient.lean` and `FixedSubringValuation.lean`; statements are on the Library's
`Langlands.Ramification.lowerGroup`; names follow the Library; no options are set.
The paired Markdown file lists the changes.
-/

import Langlands.LocalFactor.Ramification.FixedSubringValuation
import Langlands.LocalFactor.Ramification.Herbrand.CosetDepth
import Langlands.LocalFactor.Ramification.Herbrand.RationalQuotient
import Langlands.LocalFactor.Ramification.Monogenic
import Mathlib.Data.ENat.BigOperators

/-!
# Herbrand's theorem: lower groups of a quotient

Herbrand's theorem for a finite group acting on a discrete valuation ring: for a normal subgroup
`H`, the image of the lower group `G_n` in `G ⧸ H` is the lower group of the quotient acting on the
invariants `R^H` at the index `⌈φ_H(n)⌉`, where `φ_H` is the rational Herbrand function of `H`:
`G_n H / H = (G/H)_⌈φ_H(n)⌉`. It is proved first from the coset formula for depths and the scaling of
valuations, then for monogenic rings, and finally, through the monogenicity theorem, under the
hypotheses of a finite Galois extension with separable residue field extension. The upper groups
are then compatible with quotients (`UpperGroupRatQuotientCompat`).
-/

namespace Langlands.Ramification

section

section

section

open IsLocalRing IsDiscreteValuationRing

namespace LowerQuotient

variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]
variable {H : Subgroup G} [H.Normal]

end LowerQuotient

namespace LowerQuotient

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

section HerbrandPhiCeil

variable {H : Type*} [Group H] [MulSemiringAction H R]

end HerbrandPhiCeil

variable (R G) in

def LowerHerbrandQuotientCompatCanonical (H : Subgroup G) [H.Normal]
    [IsLocalRing (FixedPoints.subring R H)] : Prop :=
  RationalQuotient.LowerHerbrandQuotientCompat R G (FixedPoints.subring R H) H

end LowerQuotient

open Langlands.Ramification.LowerQuotient

private theorem sum_range_succ_eq_sum_Icc_one_add {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), f i = (∑ i ∈ Finset.Icc 1 n, f i) + f 0 := by
  induction n with
  | zero =>
    rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) from Finset.Icc_eq_empty (by omega),
      Finset.sum_empty, zero_add, Finset.sum_range_one, zero_add]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    exact add_right_comm _ _ _

namespace LowerQuotient

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem addVal_sub_swap (x y : R) : addVal R (x - y) = addVal R (y - x) :=
  (addVal R).map_sub_swap x y

variable {G : Type*} [Group G] [MulSemiringAction G R]

theorem ramificationDepth_le_addVal_smul_sub (σ : G) (x : R) :
    ramificationDepth R G σ ≤ addVal R (σ • x - x) := by
  rw [ramificationDepth_def]
  exact iInf_le _ x

theorem le_ramificationDepth {σ : G} {c : ℕ∞}
    (h : ∀ x : R, c ≤ addVal R (σ • x - x)) :
    c ≤ ramificationDepth R G σ := by
  rw [ramificationDepth_def]
  exact le_iInf h

theorem addVal_inv_smul_sub (σ : G) (x : R) :
    addVal R (σ⁻¹ • x - x) = addVal R (σ • x - x) := by
  rw [← addVal_smul σ (σ⁻¹ • x - x), smul_sub, smul_inv_smul, addVal_sub_swap]

theorem ramificationDepth_mul (σ τ : G) :
    min (ramificationDepth R G σ) (ramificationDepth R G τ) ≤
      ramificationDepth R G (σ * τ) :=
  le_ramificationDepth fun x => by
    have key : (σ * τ) • x - x = (σ • τ • x - τ • x) + (τ • x - x) := by
      rw [mul_smul, sub_add_sub_cancel]
    rw [key]
    exact le_trans (min_le_min (ramificationDepth_le_addVal_smul_sub σ (τ • x))
      (ramificationDepth_le_addVal_smul_sub τ x)) addVal_add

theorem ramificationDepth_inv (σ : G) :
    ramificationDepth R G σ⁻¹ = ramificationDepth R G σ := by
  rw [ramificationDepth_def, ramificationDepth_def]
  exact iInf_congr fun x => addVal_inv_smul_sub σ x

theorem ramificationDepth_eq_of_forall_smul_eq {H : Type*} [Group H] [MulSemiringAction H R]
    (f : H →* G) (hf : ∀ (h : H) (x : R), f h • x = h • x) (σ : H) :
    ramificationDepth R H σ = ramificationDepth R G (f σ) := by
  rw [ramificationDepth_def, ramificationDepth_def]
  exact iInf_congr fun x => by rw [hf σ x]

theorem mem_lowerGroup_iff_lt_ramificationDepth {i : ℕ} {σ : G} :
    σ ∈ lowerGroup R G i ↔ (i : ℕ∞) < ramificationDepth R G σ := by
  rw [mem_lowerGroup_iff_le_ramificationDepth,
    ENat.add_one_le_iff (ENat.natCast_ne_top i)]

theorem lowerGroupCard_eq_card_lt_ramificationDepth (i : ℕ) :
    lowerGroupCard R G i =
      Nat.card {σ : G // (i : ℕ∞) < ramificationDepth R G σ} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ =>
    mem_lowerGroup_iff_lt_ramificationDepth)

theorem sum_lowerGroupCard_eq_sum_toNat_min_ramificationDepth [Fintype G] (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), lowerGroupCard R G i =
      ∑ σ : G, (min (ramificationDepth R G σ) ((n : ℕ∞) + 1)).toNat := by
  classical

  have key : ∀ (d : ℕ∞) (N : ℕ),
      (min d (N : ℕ∞)).toNat = ∑ i ∈ Finset.range N, if (i : ℕ∞) < d then 1 else 0 := by
    intro d N
    induction N with
    | zero =>
      rw [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, min_eq_right zero_le,
        ENat.toNat_zero]
    | succ N ih =>
      rw [Finset.sum_range_succ, ← ih]
      by_cases h : (N : ℕ∞) < d
      · have h1 : ((N + 1 : ℕ) : ℕ∞) ≤ d := by
          rw [Nat.cast_add_one]
          exact (ENat.add_one_le_iff (ENat.natCast_ne_top N)).mpr h
        rw [ite_eq_left h, min_eq_right h1, min_eq_right h.le, ENat.toNat_natCast, ENat.toNat_natCast]
      · have hd : d ≤ (N : ℕ∞) := not_lt.mp h
        have h2 : d ≤ ((N + 1 : ℕ) : ℕ∞) := by
          rw [Nat.cast_add_one]
          exact hd.trans le_self_add
        rw [ite_eq_right h, min_eq_left h2, min_eq_left hd, add_zero]

  have count : ∀ i : ℕ,
      (∑ σ : G, if (i : ℕ∞) < ramificationDepth R G σ then 1 else 0) =
        lowerGroupCard R G i := by
    intro i
    rw [Finset.sum_boole, Nat.cast_id, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact (lowerGroupCard_eq_card_lt_ramificationDepth i).symm
  calc ∑ i ∈ Finset.range (n + 1), lowerGroupCard R G i
      = ∑ i ∈ Finset.range (n + 1), ∑ σ : G,
          if (i : ℕ∞) < ramificationDepth R G σ then 1 else 0 :=
        Finset.sum_congr rfl fun i _ => (count i).symm
    _ = ∑ σ : G, ∑ i ∈ Finset.range (n + 1),
          if (i : ℕ∞) < ramificationDepth R G σ then 1 else 0 := Finset.sum_comm
    _ = ∑ σ : G, (min (ramificationDepth R G σ) ((n : ℕ∞) + 1)).toNat := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [← Nat.cast_add_one]
        exact (key (ramificationDepth R G σ) (n + 1)).symm

theorem lowerGroupCard_zero_mul_herbrandPhiRat_natCast_add_one [Fintype G] (n : ℕ) :
    (lowerGroupCard R G 0 : ℚ) * (herbrandPhiRat R G (n : ℚ) + 1) =
      ∑ σ : G, ((min (ramificationDepth R G σ) ((n : ℕ∞) + 1)).toNat : ℚ) := by
  have hg0 : (0 : ℚ) < (lowerGroupCard R G 0 : ℚ) :=
    Nat.cast_pos.mpr (lowerGroupCard_pos (R := R) (G := G) 0)
  have hcast : ∑ i ∈ Finset.range (n + 1), (lowerGroupCard R G i : ℚ) =
      ∑ σ : G, ((min (ramificationDepth R G σ) ((n : ℕ∞) + 1)).toNat : ℚ) := by
    have h := congrArg (fun k : ℕ => (k : ℚ))
      (sum_lowerGroupCard_eq_sum_toNat_min_ramificationDepth (R := R) (G := G) n)
    push_cast at h
    exact h
  have hphi : herbrandPhiRat R G (n : ℚ) * (lowerGroupCard R G 0 : ℚ) =
      ∑ i ∈ Finset.Icc 1 n, (lowerGroupCard R G i : ℚ) :=
    (eq_div_iff hg0.ne').mp (herbrandPhiRat_natCast (R := R) (G := G) n)
  calc (lowerGroupCard R G 0 : ℚ) * (herbrandPhiRat R G (n : ℚ) + 1)
      = herbrandPhiRat R G (n : ℚ) * (lowerGroupCard R G 0 : ℚ) +
          (lowerGroupCard R G 0 : ℚ) := by ring
    _ = (∑ i ∈ Finset.Icc 1 n, (lowerGroupCard R G i : ℚ)) +
          (lowerGroupCard R G 0 : ℚ) := by rw [hphi]
    _ = ∑ i ∈ Finset.range (n + 1), (lowerGroupCard R G i : ℚ) :=
        (sum_range_succ_eq_sum_Icc_one_add (fun i => (lowerGroupCard R G i : ℚ)) n).symm
    _ = ∑ σ : G, ((min (ramificationDepth R G σ) ((n : ℕ∞) + 1)).toNat : ℚ) := hcast

theorem ramificationDepth_mul_eq_right_of_lt {σ τ : G}
    (h : ramificationDepth R G τ < ramificationDepth R G σ) :
    ramificationDepth R G (σ * τ) = ramificationDepth R G τ := by
  refine le_antisymm ?_ ?_
  · by_contra hlt
    rw [not_le] at hlt
    have hkey := ramificationDepth_mul (R := R) σ⁻¹ (σ * τ)
    rw [inv_mul_cancel_left, ramificationDepth_inv] at hkey
    exact absurd hkey (not_le.mpr (lt_min h hlt))
  · have hmul := ramificationDepth_mul (R := R) σ τ
    rwa [min_eq_right h.le] at hmul

theorem fixedSubringRamificationDepth_one (H : Subgroup G) [H.Normal] :
    CosetDepth.fixedSubringRamificationDepth R G H 1 = ⊤ := by
  rw [CosetDepth.fixedSubringRamificationDepth_def]
  simp only [one_smul, sub_self, ZeroMemClass.coe_zero, addVal_zero, iInf_top]

theorem ramificationDepth_le_fixedSubringRamificationDepth (H : Subgroup G) [H.Normal]
    (τ : G) :
    ramificationDepth R G τ ≤ CosetDepth.fixedSubringRamificationDepth R G H (QuotientGroup.mk τ) := by
  rw [CosetDepth.fixedSubringRamificationDepth_def]
  refine le_iInf fun x => ?_
  rw [CosetDepth.coe_quotientMk_smul_sub_fixedSubring]
  exact ramificationDepth_le_addVal_smul_sub τ (x : R)

theorem ramificationDepth_subgroup_coe {H : Subgroup G} (h : H) :
    ramificationDepth R H h = ramificationDepth R G (h : G) :=
  ramificationDepth_eq_of_forall_smul_eq H.subtype (fun _ _ => rfl) h

theorem cosetRamificationDepthSum_eq_top_of_mem {H : Subgroup G} [Fintype H] {τ₀ : G}
    (h : τ₀ ∈ H) :
    CosetDepth.cosetRamificationDepthSum R G H τ₀ = ⊤ := by
  rw [CosetDepth.cosetRamificationDepthSum_def, ENat.sum_eq_top]
  refine ⟨⟨τ₀⁻¹, H.inv_mem h⟩, Finset.mem_univ _, ?_⟩
  show ramificationDepth R G (τ₀ * τ₀⁻¹) = ⊤
  rw [mul_inv_cancel]
  exact ramificationDepth_one

theorem cosetRamificationDepthSum_ne_top {H : Subgroup G} [H.Normal] [Fintype H]
    [FaithfulSMul G R] {τ₀ : G} (h : (QuotientGroup.mk τ₀ : G ⧸ H) ≠ 1) :
    CosetDepth.cosetRamificationDepthSum R G H τ₀ ≠ ⊤ := by
  rw [CosetDepth.cosetRamificationDepthSum_def]
  intro htop
  rw [ENat.sum_eq_top] at htop
  obtain ⟨h', -, hh'⟩ := htop
  refine h ?_
  rw [QuotientGroup.eq_one_iff]
  have h1 : τ₀ * (h' : G) = 1 := by
    have := ramificationDepth_eq_top_iff (R := R) (G := G) (σ := τ₀ * (h' : G))
    exact this.mp hh'
  rw [eq_inv_of_mul_eq_one_left h1]
  exact H.inv_mem h'.2

theorem ramificationDepth_mul_coe_eq_min {H : Subgroup G} {τ₀ : G}
    (hmax : ∀ h : H, ramificationDepth R G (τ₀ * (h : G)) ≤ ramificationDepth R G τ₀)
    (h : H) :
    ramificationDepth R G (τ₀ * (h : G)) =
      min (ramificationDepth R G (h : G)) (ramificationDepth R G τ₀) := by
  rcases lt_or_ge (ramificationDepth R G (h : G)) (ramificationDepth R G τ₀) with hlt | hge
  · rw [min_eq_left hlt.le]
    exact ramificationDepth_mul_eq_right_of_lt hlt
  · rw [min_eq_right hge]
    refine le_antisymm (hmax h) ?_
    have hmul := ramificationDepth_mul (R := R) τ₀ (h : G)
    rwa [min_eq_left hge] at hmul

theorem exists_max_ramificationDepth_coset {H : Subgroup G} [Finite H] (τ₀ : G) :
    ∃ h₀ : H, ∀ h : H,
      ramificationDepth R G (τ₀ * (h : G)) ≤ ramificationDepth R G (τ₀ * (h₀ : G)) := by
  haveI : Nonempty H := ⟨1⟩
  exact Finite.exists_max fun h : H => ramificationDepth R G (τ₀ * (h : G))

theorem exists_quotientMk_eq_max_ramificationDepth {H : Subgroup G} [Finite H] (τ₀ : G) :
    ∃ τ₁ : G, (QuotientGroup.mk τ₁ : G ⧸ H) = QuotientGroup.mk τ₀ ∧
      ∀ h : H, ramificationDepth R G (τ₁ * (h : G)) ≤ ramificationDepth R G τ₁ := by
  obtain ⟨h₀, hh₀⟩ := exists_max_ramificationDepth_coset (R := R) (H := H) τ₀
  refine ⟨τ₀ * (h₀ : G), QuotientGroup.mk_mul_of_mem τ₀ h₀.2, fun h => ?_⟩
  have hassoc : (τ₀ * (h₀ : G)) * (h : G) = τ₀ * ((h₀ * h : H) : G) := by
    rw [Subgroup.coe_mul, mul_assoc]
  rw [hassoc]
  exact hh₀ (h₀ * h)

theorem sum_toNat_ramificationDepth_coset_eq {H : Subgroup G} [Fintype H] {τ₀ : G} {n : ℕ}
    (hτ₀ : ramificationDepth R G τ₀ = (n : ℕ∞) + 1)
    (hmax : ∀ h : H, ramificationDepth R G (τ₀ * (h : G)) ≤ ramificationDepth R G τ₀) :
    ∑ h : H, ((ramificationDepth R G (τ₀ * (h : G))).toNat : ℚ) =
      (lowerGroupCard R H 0 : ℚ) * (herbrandPhiRat R H (n : ℚ) + 1) := by
  have hbridge : (lowerGroupCard R H 0 : ℚ) * (herbrandPhiRat R H (n : ℚ) + 1) =
      ∑ h : H, ((min (ramificationDepth R H h) ((n : ℕ∞) + 1)).toNat : ℚ) :=
    lowerGroupCard_zero_mul_herbrandPhiRat_natCast_add_one n
  rw [hbridge]
  refine Finset.sum_congr rfl fun h _ => ?_
  have key : ramificationDepth R G (τ₀ * (h : G)) =
      min (ramificationDepth R H h) ((n : ℕ∞) + 1) := by
    rw [ramificationDepth_mul_coe_eq_min hmax h, hτ₀, ramificationDepth_subgroup_coe h]
  rw [key]

theorem cosetRamificationDepthSum_toNat_eq {H : Subgroup G} [Fintype H] {τ₀ : G} {n : ℕ}
    (hτ₀ : ramificationDepth R G τ₀ = (n : ℕ∞) + 1)
    (hmax : ∀ h : H, ramificationDepth R G (τ₀ * (h : G)) ≤ ramificationDepth R G τ₀) :
    ((CosetDepth.cosetRamificationDepthSum R G H τ₀).toNat : ℚ) =
      (lowerGroupCard R H 0 : ℚ) * (herbrandPhiRat R H (n : ℚ) + 1) := by
  have hne : ∀ h : H, ramificationDepth R G (τ₀ * (h : G)) ≠ ⊤ := by
    intro h
    refine ne_top_of_le_ne_top ?_ (hmax h)
    rw [hτ₀, ← Nat.cast_add_one]
    exact ENat.natCast_ne_top _
  rw [CosetDepth.cosetRamificationDepthSum_def, ENat.toNat_sum (fun h _ => hne h)]
  push_cast
  exact sum_toNat_ramificationDepth_coset_eq hτ₀ hmax

theorem cosetRamificationDepthSum_eq_zero_of_eq_zero {H : Subgroup G} [Fintype H] {τ₀ : G}
    (hτ₀ : ramificationDepth R G τ₀ = 0)
    (hmax : ∀ h : H, ramificationDepth R G (τ₀ * (h : G)) ≤ ramificationDepth R G τ₀) :
    CosetDepth.cosetRamificationDepthSum R G H τ₀ = 0 := by
  rw [CosetDepth.cosetRamificationDepthSum_def]
  refine Finset.sum_eq_zero fun h _ => ?_
  exact le_antisymm (hτ₀ ▸ hmax h) zero_le

namespace RamificationDepthCosetLemma

theorem fixedSubringRamificationDepth_ne_top {H : Subgroup G} [H.Normal] [Fintype H]
    [FaithfulSMul G R] (hc : CosetDepth.RamificationDepthCosetLemma R G H) {τ₀ : G}
    (h : (QuotientGroup.mk τ₀ : G ⧸ H) ≠ 1) :
    CosetDepth.fixedSubringRamificationDepth R G H (QuotientGroup.mk τ₀) ≠ ⊤ := by
  rw [hc τ₀]
  exact cosetRamificationDepthSum_ne_top h

theorem toNat_fixedSubringRamificationDepth_eq {H : Subgroup G} [H.Normal] [Fintype H]
    (hc : CosetDepth.RamificationDepthCosetLemma R G H) {τ₀ : G} {n : ℕ}
    (hτ₀ : ramificationDepth R G τ₀ = (n : ℕ∞) + 1)
    (hmax : ∀ h : H, ramificationDepth R G (τ₀ * (h : G)) ≤ ramificationDepth R G τ₀) :
    ((CosetDepth.fixedSubringRamificationDepth R G H (QuotientGroup.mk τ₀)).toNat : ℚ) =
      (lowerGroupCard R H 0 : ℚ) * (herbrandPhiRat R H (n : ℚ) + 1) := by
  rw [hc τ₀]
  exact cosetRamificationDepthSum_toNat_eq hτ₀ hmax

end RamificationDepthCosetLemma

section SerreDisplay

variable {H : Subgroup G} [H.Normal]
variable [IsDiscreteValuationRing (FixedPoints.subring R H)]

theorem fixedSubringRamificationDepth_eq_mul_ramificationDepth {e : ℕ}
    (hscale : ∀ y : FixedPoints.subring R H,
      addVal R (y : R) = (e : ℕ∞) * addVal (FixedPoints.subring R H) y)
    (σ : G ⧸ H) :
    CosetDepth.fixedSubringRamificationDepth R G H σ =
      (e : ℕ∞) * ramificationDepth (FixedPoints.subring R H) (G ⧸ H) σ := by
  haveI : Nonempty (FixedPoints.subring R H) := ⟨0⟩
  rw [CosetDepth.fixedSubringRamificationDepth_def, ramificationDepth_def, ENat.mul_iInf]
  exact iInf_congr fun x => hscale _

theorem RamificationDepthCosetLemma.mul_ramificationDepth_eq_cosetSum [Fintype H] {e : ℕ}
    (hc : CosetDepth.RamificationDepthCosetLemma R G H)
    (hscale : ∀ y : FixedPoints.subring R H,
      addVal R (y : R) = (e : ℕ∞) * addVal (FixedPoints.subring R H) y)
    (τ₀ : G) :
    (e : ℕ∞) * ramificationDepth (FixedPoints.subring R H) (G ⧸ H) (QuotientGroup.mk τ₀) =
      CosetDepth.cosetRamificationDepthSum R G H τ₀ := by
  rw [← fixedSubringRamificationDepth_eq_mul_ramificationDepth hscale]
  exact hc τ₀

theorem RamificationDepthCosetLemma.toNat_ramificationDepth_quotient_eq [Fintype H] {e : ℕ}
    (hc : CosetDepth.RamificationDepthCosetLemma R G H)
    (hscale : ∀ y : FixedPoints.subring R H,
      addVal R (y : R) = (e : ℕ∞) * addVal (FixedPoints.subring R H) y)
    (he : e = lowerGroupCard R H 0) {τ₀ : G} {n : ℕ}
    (hτ₀ : ramificationDepth R G τ₀ = (n : ℕ∞) + 1)
    (hmax : ∀ h : H, ramificationDepth R G (τ₀ * (h : G)) ≤ ramificationDepth R G τ₀) :
    ((ramificationDepth (FixedPoints.subring R H) (G ⧸ H) (QuotientGroup.mk τ₀)).toNat : ℚ) =
      herbrandPhiRat R H (n : ℚ) + 1 := by
  have hpos : 0 < lowerGroupCard R H 0 := lowerGroupCard_pos 0
  have he0 : (lowerGroupCard R H 0 : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  have hsum := cosetRamificationDepthSum_toNat_eq (H := H) hτ₀ hmax
  rw [← (RamificationDepthCosetLemma.mul_ramificationDepth_eq_cosetSum hc) hscale τ₀, ENat.toNat_mul] at hsum
  have hcoe : ((e : ℕ∞)).toNat = e := by simp
  rw [hcoe] at hsum
  push_cast at hsum
  rw [he] at hsum
  exact mul_left_cancel₀ he0 hsum

end SerreDisplay

section FromCosetLemma

variable {H : Subgroup G} [H.Normal] [Fintype H]

theorem mem_lowerGroup_map_iff_max_depth {τ₀ : G} {n : ℕ}
    (hmax : ∀ h : H, ramificationDepth R G (τ₀ * (h : G)) ≤ ramificationDepth R G τ₀) :
    (QuotientGroup.mk τ₀ : G ⧸ H) ∈
        (lowerGroup R G n).map (QuotientGroup.mk' H) ↔
      (n : ℕ∞) + 1 ≤ ramificationDepth R G τ₀ := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨σ, hσn, hσcls⟩
    have hh : τ₀⁻¹ * σ ∈ H :=
      QuotientGroup.eq.mp ((QuotientGroup.mk'_apply H σ ▸ hσcls).symm)
    have hσeq : σ = τ₀ * (τ₀⁻¹ * σ) := by group
    exact le_trans (mem_lowerGroup_iff_le_ramificationDepth.mp hσn)
      (hσeq ▸ hmax ⟨τ₀⁻¹ * σ, hh⟩)
  · intro hle
    exact ⟨τ₀, mem_lowerGroup_iff_le_ramificationDepth.mpr hle, rfl⟩

section SerreDisplay

variable [FaithfulSMul G R] [IsDiscreteValuationRing (FixedPoints.subring R H)]

namespace RamificationDepthCosetLemma

theorem ramificationDepth_quotient_ne_top (hc : CosetDepth.RamificationDepthCosetLemma R G H)
    (hscale : ∀ y : FixedPoints.subring R H,
      addVal R (y : R) = (lowerGroupCard R H 0 : ℕ∞) *
        addVal (FixedPoints.subring R H) y)
    {τ₀ : G} (hne : (QuotientGroup.mk τ₀ : G ⧸ H) ≠ 1) :
    ramificationDepth (FixedPoints.subring R H) (G ⧸ H) (QuotientGroup.mk τ₀) ≠ ⊤ := by
  have hfix := (RamificationDepthCosetLemma.fixedSubringRamificationDepth_ne_top hc) hne
  rw [fixedSubringRamificationDepth_eq_mul_ramificationDepth hscale] at hfix
  intro habs
  refine hfix ?_
  rw [habs, ENat.mul_top]
  exact_mod_cast (lowerGroupCard_pos (R := R) (G := H) 0).ne'

theorem ramificationDepth_quotient_eq_zero (hc : CosetDepth.RamificationDepthCosetLemma R G H)
    (hscale : ∀ y : FixedPoints.subring R H,
      addVal R (y : R) = (lowerGroupCard R H 0 : ℕ∞) *
        addVal (FixedPoints.subring R H) y)
    {τ₀ : G} (hτ₀ : ramificationDepth R G τ₀ = 0)
    (hmax : ∀ h : H, ramificationDepth R G (τ₀ * (h : G)) ≤ ramificationDepth R G τ₀) :
    ramificationDepth (FixedPoints.subring R H) (G ⧸ H) (QuotientGroup.mk τ₀) = 0 := by
  have hfix := (fixedSubringRamificationDepth_eq_mul_ramificationDepth hscale
    (QuotientGroup.mk τ₀)).symm.trans
    ((hc τ₀).trans (cosetRamificationDepthSum_eq_zero_of_eq_zero hτ₀ hmax))
  rcases mul_eq_zero.mp hfix with h | h
  · exact absurd h (by exact_mod_cast (lowerGroupCard_pos (R := R) (G := H) 0).ne')
  · exact h

theorem depth_iff_depth (hc : CosetDepth.RamificationDepthCosetLemma R G H)
    (hscale : ∀ y : FixedPoints.subring R H,
      addVal R (y : R) = (lowerGroupCard R H 0 : ℕ∞) *
        addVal (FixedPoints.subring R H) y)
    {τ₀ : G} (hne : (QuotientGroup.mk τ₀ : G ⧸ H) ≠ 1)
    (hmax : ∀ h : H, ramificationDepth R G (τ₀ * (h : G)) ≤ ramificationDepth R G τ₀)
    (n : ℕ) :
    (n : ℕ∞) + 1 ≤ ramificationDepth R G τ₀ ↔
      (RationalQuotient.herbrandPhiRatCeil R H n : ℕ∞) + 1 ≤
        ramificationDepth (FixedPoints.subring R H) (G ⧸ H) (QuotientGroup.mk τ₀) := by

  have hτ₀fin : ramificationDepth R G τ₀ ≠ ⊤ := fun habs =>
    hne (by rw [ramificationDepth_eq_top_iff.mp habs]; exact QuotientGroup.mk_one H)
  have hqfin := (RamificationDepthCosetLemma.ramificationDepth_quotient_ne_top hc) hscale hne
  set d := (ramificationDepth R G τ₀).toNat with hddef
  set k := (ramificationDepth (FixedPoints.subring R H) (G ⧸ H)
    (QuotientGroup.mk τ₀)).toNat with hkdef

  rw [← ENat.natCast_toNat hτ₀fin, ← ENat.natCast_toNat hqfin, ← hddef, ← hkdef,
    show ((n : ℕ∞) + 1) = ((n + 1 : ℕ) : ℕ∞) from by push_cast; ring,
    show ((RationalQuotient.herbrandPhiRatCeil R H n : ℕ∞) + 1) =
      ((RationalQuotient.herbrandPhiRatCeil R H n + 1 : ℕ) : ℕ∞) from by push_cast; ring,
    Nat.cast_le, Nat.cast_le]

  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  ·
    have hτ₀ : ramificationDepth R G τ₀ = 0 := by
      rw [← ENat.natCast_toNat hτ₀fin, ← hddef, hd0, Nat.cast_zero]
    have hk0 : k = 0 := by
      rw [hkdef, (RamificationDepthCosetLemma.ramificationDepth_quotient_eq_zero hc) hscale hτ₀ hmax]; rfl
    simp [hd0, hk0]
  ·
    obtain ⟨m, hmd⟩ : ∃ m, d = m + 1 := ⟨d - 1, (Nat.sub_add_cancel hdpos).symm⟩
    have hm : ramificationDepth R G τ₀ = (m : ℕ∞) + 1 := by
      rw [← ENat.natCast_toNat hτ₀fin, ← hddef, hmd]; push_cast; ring
    have hlemme5 := (RamificationDepthCosetLemma.toNat_ramificationDepth_quotient_eq hc) hscale rfl hm hmax
    rw [← hkdef] at hlemme5
    have hk1 : 1 ≤ k := by
      have : (1 : ℚ) ≤ (k : ℚ) := by
        rw [hlemme5]; linarith [herbrandPhiRat_nonneg (R := R) (G := H) (Nat.cast_nonneg m)]
      exact_mod_cast this
    have hφm : herbrandPhiRat R H (m : ℚ) = ((k - 1 : ℕ) : ℚ) := by
      rw [Nat.cast_sub hk1, hlemme5]; ring
    rw [hmd, RationalQuotient.herbrandPhiRatCeil_eq_ceil, ← Nat.le_sub_iff_add_le hk1,
      Nat.ceil_le, ← hφm,
      (herbrandPhiRat_strictMono (R := R) (G := H)).le_iff_le, Nat.cast_le]
    omega

end RamificationDepthCosetLemma

theorem lowerHerbrandQuotientCompatCanonical_of_cosetLemma
    (hc : CosetDepth.RamificationDepthCosetLemma R G H)
    (hscale : ∀ y : FixedPoints.subring R H,
      addVal R (y : R) = (lowerGroupCard R H 0 : ℕ∞) *
        addVal (FixedPoints.subring R H) y) :
    LowerHerbrandQuotientCompatCanonical R G H := by
  intro n
  ext σ
  obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective σ
  by_cases hne : (QuotientGroup.mk τ : G ⧸ H) = 1
  · rw [hne]; exact iff_of_true (Subgroup.one_mem _) (Subgroup.one_mem _)
  · obtain ⟨τ₀, hcls, hmax⟩ :=
      exists_quotientMk_eq_max_ramificationDepth (R := R) (H := H) τ
    rw [← hcls, mem_lowerGroup_map_iff_max_depth hmax,
      mem_lowerGroup_iff_le_ramificationDepth]
    exact (RamificationDepthCosetLemma.depth_iff_depth hc) hscale (hcls ▸ hne) hmax n

end SerreDisplay

end FromCosetLemma

end LowerQuotient

end

theorem map_lowerGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [FaithfulSMul G R]
    {H : Subgroup G} [H.Normal] [Fintype H] [IsDiscreteValuationRing (FixedPoints.subring R H)]
    (hH : ∀ τ : G,
      (⨅ z : FixedPoints.subring R H,
          IsDiscreteValuationRing.addVal R
            (((QuotientGroup.mk τ : G ⧸ H) • z - z : FixedPoints.subring R H) : R)) =
        ∑ h : H, ramificationDepth R G (τ * (h : G)))
    (he : ∀ z : FixedPoints.subring R H,
      IsDiscreteValuationRing.addVal R (z : R) =
        (lowerGroupCard R H 0 : ℕ∞) *
          IsDiscreteValuationRing.addVal (FixedPoints.subring R H) z)
    (n : ℕ) :
    (lowerGroup R G n).map (QuotientGroup.mk' H) =
      lowerGroup (FixedPoints.subring R H) (G ⧸ H)
        ⌈herbrandPhiRat R H (n : ℚ)⌉₊ := by
  have h := LowerQuotient.lowerHerbrandQuotientCompatCanonical_of_cosetLemma
    (R := R) (G := G) (H := H) hH he n
  rwa [RationalQuotient.herbrandPhiRatCeil_eq_ceil] at h

end

end

section

section
attribute [-instance] isLocalRing_fixedSubring isLocalHom_fixedSubring_subtype

theorem map_lowerGroup_mk_eq_of_adjoin_singleton_eq_top
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [FaithfulSMul G R]
    {A : Type*} [CommSemiring A] [Algebra A R]
    (hA : ∀ (σ : G) (a : A), σ • algebraMap A R a = algebraMap A R a)
    {H : Subgroup G} [H.Normal] [Fintype H] [IsDiscreteValuationRing (FixedPoints.subring R H)]
    {x : R} (hx : Algebra.adjoin A {x} = ⊤)
    {y : R} (hy : y ∈ FixedPoints.subring R H)
    (hy' : ∀ z ∈ FixedPoints.subring R H, z ∈ Algebra.adjoin A {y})
    (he : ∀ z : FixedPoints.subring R H,
      IsDiscreteValuationRing.addVal R (z : R) =
        (lowerGroupCard R H 0 : ℕ∞) *
          IsDiscreteValuationRing.addVal (FixedPoints.subring R H) z)
    (n : ℕ) :
    (lowerGroup R G n).map (QuotientGroup.mk' H) =
      lowerGroup (FixedPoints.subring R H) (G ⧸ H)
        ⌈herbrandPhiRat R H (n : ℚ)⌉₊ :=
  map_lowerGroup_mk_eq_of_iInf_addVal_smul_sub_eq_sum_ramificationDepth
    (iInf_addVal_smul_sub_eq_sum_ramificationDepth_of_adjoin_singleton_eq_top
      hA hx hy hy')
    he n

end

end

section

section

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace LowerQuotient

end LowerQuotient

theorem map_lowerGroup_mk_eq_of_isSeparable_residueField
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    {H : Subgroup G} [H.Normal] (n : ℕ) :
    (lowerGroup R G n).map (QuotientGroup.mk' H) =
      lowerGroup (FixedPoints.subring R H) (G ⧸ H)
        ⌈herbrandPhiRat R H (n : ℚ)⌉₊ := by
  classical
  haveI : Fintype H := Fintype.ofFinite _

  haveI : IsDiscreteValuationRing (FixedPoints.subring R G) :=
    isDiscreteValuationRing_fixedSubring
  haveI : IsDiscreteValuationRing (FixedPoints.subring R H) :=
    isDiscreteValuationRing_fixedSubring

  haveI : Module.Finite (FixedPoints.subring R G) R :=
    FixedSubringValuation.module_finite_fixedSubring

  haveI hlocG : IsLocalHom (algebraMap (FixedPoints.subring R G) R) :=
    ⟨fun a h => (isUnit_fixedSubring_iff a).mpr h⟩

  haveI : Algebra.IsSeparable (ResidueField (FixedPoints.subring R G)) (ResidueField R) :=
    (inferInstance : Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R))

  obtain ⟨x, hx⟩ :=
    exists_adjoin_singleton_eq_top_of_isSeparable_residueField
      (A := FixedPoints.subring R G) (B := R) Subtype.val_injective

  have hle : FixedPoints.subring R G ≤ FixedPoints.subring R H := fun a ha h => ha (h : G)
  letI algAH : Algebra (FixedPoints.subring R G) (FixedPoints.subring R H) :=
    (Subring.inclusion hle).toAlgebra
  haveI : IsScalarTower (FixedPoints.subring R G) (FixedPoints.subring R H) R :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Finite (FixedPoints.subring R G) (FixedPoints.subring R H) :=
    Module.Finite.of_injective
      (IsScalarTower.toAlgHom (FixedPoints.subring R G) (FixedPoints.subring R H) R).toLinearMap
      Subtype.val_injective
  haveI hlocH : IsLocalHom (algebraMap (FixedPoints.subring R H) R) :=
    ⟨fun a h => (isUnit_fixedSubring_iff a).mpr h⟩
  haveI hlocGH : IsLocalHom (algebraMap (FixedPoints.subring R G) (FixedPoints.subring R H)) :=
    ⟨fun a h => (isUnit_fixedSubring_iff a).mpr
      ((isUnit_fixedSubring_iff (Subring.inclusion hle a)).mp h)⟩
  haveI : Algebra.IsSeparable (ResidueField (FixedPoints.subring R G))
      (ResidueField (FixedPoints.subring R H)) :=
    Algebra.IsSeparable.of_algHom _ _
      (IsScalarTower.toAlgHom (ResidueField (FixedPoints.subring R G))
        (ResidueField (FixedPoints.subring R H)) (ResidueField R))
  obtain ⟨y', hy'⟩ :=
    exists_adjoin_singleton_eq_top_of_isSeparable_residueField
      (A := FixedPoints.subring R G) (B := FixedPoints.subring R H)
      (fun a b h => Subtype.ext (congrArg Subtype.val h :))
  have hyadj : ∀ z ∈ FixedPoints.subring R H,
      z ∈ Algebra.adjoin (FixedPoints.subring R G) {(y' : R)} := fun z hz => by
    have h1 : (⟨z, hz⟩ : FixedPoints.subring R H) ∈
        Algebra.adjoin (FixedPoints.subring R G) {y'} := hy' ▸ Algebra.mem_top
    have h2 : IsScalarTower.toAlgHom (FixedPoints.subring R G) (FixedPoints.subring R H) R ⟨z, hz⟩ ∈
        (Algebra.adjoin (FixedPoints.subring R G) {y'}).map
          (IsScalarTower.toAlgHom (FixedPoints.subring R G) (FixedPoints.subring R H) R) :=
      Subalgebra.mem_map.mpr ⟨_, h1, rfl⟩
    rwa [AlgHom.map_adjoin_singleton] at h2

  haveI : (IsLocalRing.maximalIdeal R).LiesOver
      (IsLocalRing.maximalIdeal (FixedPoints.subring R H)) :=
    ⟨maximalIdeal_fixedSubring_eq_comap⟩
  haveI : Algebra.IsSeparable
      (FixedPoints.subring R H ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R H))
      (R ⧸ IsLocalRing.maximalIdeal R) :=
    (Algebra.isSeparable_tower_top_of_isSeparable (ResidueField (FixedPoints.subring R G))
      (ResidueField (FixedPoints.subring R H)) (ResidueField R) :)
  have he := fun z : FixedPoints.subring R H =>
    addVal_coe_eq_lowerGroupCard_zero_mul_addVal_fixedPoints
      (R := R) (H := H) z

  exact map_lowerGroup_mk_eq_of_adjoin_singleton_eq_top
    (A := FixedPoints.subring R G) (fun σ a => a.2 σ) hx y'.2 hyadj he n

end

end

section

section
attribute [-simp] lowerGroup_subgroupOf lowerGroup_map_subtype

theorem upperGroupRatQuotientCompat_of_isSeparable_residueField
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    (H : Subgroup G) [H.Normal] :
    UpperGroupRatQuotientCompat R G (FixedPoints.subring R H) H :=
  upperGroupRatQuotientCompat_of_map_lowerGroup_mk_eq fun n =>
    map_lowerGroup_mk_eq_of_isSeparable_residueField
      (R := R) (G := G) (H := H) n

end

end

end Langlands.Ramification
