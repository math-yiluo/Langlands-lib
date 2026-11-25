/-
Adapted from the Anthropic Lean formalisation of Fermat's Last Theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, files
`Theorems/Thm_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isCyclic.lean`,
`P2M/Sol/S_IsDiscreteValuationRing_hasseArfChain_lowerRamificationGroup_of_isCyclic.lean`.
Copyright 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: the statement file and its proof are one module; the FLT proof name spaces
`P2MW.<file>.Ws45.HATame` and `P2MW.<file>.HasseArfCyc` are `Langlands.Ramification.HasseArf.Cyclic`,
and the four lemmas of `Ws45.HATame` that the FLT proof of the tame character also carried are those
of `LowerGroupQuotients.lean`; statements are on the Library's `Langlands.Ramification.lowerGroup`;
names follow the Library; no options are set.
The paired Markdown file lists the changes.
-/

import Langlands.LocalFactor.Ramification.HasseArf.Congruence
import Langlands.LocalFactor.Ramification.HasseArf.Counting
import Langlands.LocalFactor.Ramification.HasseArf.Tame

/-!
# The Hasse–Arf theorem for a cyclic group

The Hasse–Arf theorem for a cyclic group acting faithfully on a discrete valuation ring with
perfect residue field (and separable residue extension over the invariants): the lower filtration
has the Hasse–Arf property, i.e. `φ` is an integer at every break. In residue characteristic `0`
there is no break `i ≥ 1` (an element of `G_i` whose order is a unit lies in `G_{i+1}`). In
characteristic `p` the counting theorem of `HasseArf/Counting.lean` applies, with `G_1` a `p`-group,
`[G_0 : G_1]` prime to `p`, the tame divisibility of `HasseArf/Tame.lean` and Sen's congruences of
`HasseArf/Congruence.lean`.
-/

namespace Langlands.Ramification

section

section

namespace HasseArf.Cyclic

open IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

local notation "Γ" => lowerGroup R G

theorem pow_add_eq_pow_of_mul_eq_zero {S : Type*} [CommRing S] (x c : S) (hxc : x * c = 0) (hcc : c * c = 0) :
    ∀ k : ℕ, 1 ≤ k → (x + c) ^ (k + 1) = x ^ (k + 1) := by
  have h1 : ∀ k : ℕ, x ^ (k + 1) * c = 0 := fun k => by rw [pow_succ, mul_assoc, hxc, mul_zero]
  have h2 : ∀ k : ℕ, (x + c) ^ (k + 1) * c = 0 := fun k => by
    rw [pow_succ, mul_assoc, add_mul, hxc, hcc, add_zero, mul_zero]
  have P : ∀ k : ℕ, x * (x + c) ^ k = x ^ (k + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc x * (x + c) ^ (k + 1) = (x * (x + c) ^ k) * (x + c) := by ring
        _ = x ^ (k + 1) * (x + c) := by rw [ih]
        _ = x ^ (k + 1) * x + x ^ (k + 1) * c := by ring
        _ = x ^ (k + 1 + 1) := by rw [h1, add_zero, ← pow_succ]
  intro k hk
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  calc (x + c) ^ (k + 1 + 1) = x * (x + c) ^ (k + 1) + (x + c) ^ (k + 1) * c := by ring
    _ = x ^ (k + 1 + 1) + 0 := by rw [P, h2]
    _ = x ^ (k + 1 + 1) := by ring

theorem smul_sub_mem_pow_of_mem_pow {ϖ : R} (hϖ : Irreducible ϖ) {s : G} {i : ℕ} (hi : 1 ≤ i)
    (hs : s ∈ Γ i) {y : R} (hy : y ∈ maximalIdeal R ^ (i + 1)) :
    s • y - y ∈ maximalIdeal R ^ (i + 2) := by
  have hs0 : s ∈ Γ 0 := (lowerGroup_antitone _ _) (Nat.zero_le i) hs
  have hmax : maximalIdeal R = Ideal.span {ϖ} := hϖ.maximalIdeal_eq

  rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hy
  obtain ⟨b, rfl⟩ := hy
  set c := s • ϖ - ϖ with hc
  have hcmem : c ∈ maximalIdeal R ^ (i + 1) := (mem_lowerGroup.1 hs) ϖ
  have hsb : s • b - b ∈ maximalIdeal R := by
    have h := (mem_lowerGroup.1 hs0) b
    rwa [zero_add, pow_one] at h
  have hϖmem : ϖ ∈ maximalIdeal R := by rw [hmax]; exact Ideal.mem_span_singleton_self ϖ

  have hsϖ : s • ϖ = ϖ + c := by rw [hc]; ring
  have e : s • (ϖ ^ (i + 1) * b) - ϖ ^ (i + 1) * b =
      ((ϖ + c) ^ (i + 1) - ϖ ^ (i + 1)) * (s • b) + ϖ ^ (i + 1) * (s • b - b) := by
    rw [smul_mul', smul_pow', hsϖ]; ring
  rw [e]
  refine Ideal.add_mem _ ?_ ?_
  · apply Ideal.mul_mem_right

    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_pow, map_add]
    have hxc : Ideal.Quotient.mk (maximalIdeal R ^ (i + 2)) ϖ * Ideal.Quotient.mk (maximalIdeal R ^ (i + 2)) c = 0 := by
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, show i + 2 = 1 + (i + 1) by ring, pow_add, pow_one]
      exact Ideal.mul_mem_mul hϖmem hcmem
    have hcc : Ideal.Quotient.mk (maximalIdeal R ^ (i + 2)) c * Ideal.Quotient.mk (maximalIdeal R ^ (i + 2)) c = 0 := by
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have := Ideal.mul_mem_mul hcmem hcmem
      rw [← pow_add] at this
      exact Ideal.pow_le_pow_right (by omega) this
    rw [pow_add_eq_pow_of_mul_eq_zero _ _ hxc hcc i hi, sub_self]
  · rw [show i + 2 = (i + 1) + 1 by ring, pow_succ]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hϖmem _) hsb

theorem pow_smul_sub_sub_nsmul_mem {ϖ : R} (hϖ : Irreducible ϖ) {s : G} {i : ℕ} (hi : 1 ≤ i) (hs : s ∈ Γ i) :
    ∀ k : ℕ, s ^ k • ϖ - ϖ - (k : R) * (s • ϖ - ϖ) ∈ maximalIdeal R ^ (i + 2) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hy : s ^ k • ϖ - ϖ ∈ maximalIdeal R ^ (i + 1) :=
      (mem_lowerGroup.1 (Subgroup.pow_mem _ hs k)) ϖ
    have h1 := smul_sub_mem_pow_of_mem_pow hϖ hi hs hy
    have e : s ^ (k + 1) • ϖ - ϖ - ((k + 1 : ℕ) : R) * (s • ϖ - ϖ) =
        (s • (s ^ k • ϖ - ϖ) - (s ^ k • ϖ - ϖ)) + (s ^ k • ϖ - ϖ - (k : R) * (s • ϖ - ϖ)) := by
      rw [pow_succ', mul_smul, smul_sub]; push_cast; ring
    rw [e]
    exact Ideal.add_mem _ h1 ih

theorem mem_succ_of_mem_of_isUnit [Finite G] [PerfectField (ResidueField R)]
    {s : G} {i : ℕ} (hi : 1 ≤ i) (hs : s ∈ Γ i) (hunit : IsUnit ((orderOf s : ℕ) : R)) :
    s ∈ Γ (i + 1) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hs0 : s ∈ Γ 0 := (lowerGroup_antitone _ _) (Nat.zero_le i) hs
  have key := pow_smul_sub_sub_nsmul_mem hϖ hi hs (orderOf s)
  rw [pow_orderOf_eq_one, one_smul, sub_self, zero_sub, neg_mem_iff] at key
  have hc : s • ϖ - ϖ ∈ maximalIdeal R ^ (i + 1 + 1) :=
    (Ideal.unit_mul_mem_iff_mem _ hunit).1 key
  exact (LowerGroupQuotients.mem_lowerGroup_iff_smul_uniformizer_sub_mem_pow hϖ hs0 (i + 1)).2 hc

end HasseArf.Cyclic

theorem hasseArfChain_lowerGroup_of_isCyclic
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [IsCyclic G]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    [PerfectField (IsLocalRing.ResidueField R)] :
    HasseArfChain (lowerGroup R G) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  obtain ⟨p, hchar⟩ := CharP.exists (IsLocalRing.ResidueField R)
  haveI := hchar
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  ·
    haveI : CharZero (IsLocalRing.ResidueField R) := CharP.charP_to_charZero _
    intro i hjump
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · exfalso
      apply hjump
      refine le_antisymm ?_ ((lowerGroup_antitone _ _) (Nat.le_succ i))
      intro s hs
      refine HasseArf.Cyclic.mem_succ_of_mem_of_isUnit hi hs ?_

      have hn : ((orderOf s : ℕ) : R) ∉ IsLocalRing.maximalIdeal R := by
        rw [← IsLocalRing.residue_eq_zero_iff, map_natCast, Nat.cast_eq_zero]
        exact (orderOf_pos s).ne'
      exact (IsLocalRing.notMem_maximalIdeal.1 hn)
  ·
    have hp : p.Prime := (CharP.char_is_prime_or_zero (IsLocalRing.ResidueField R) p).resolve_right hp0.ne'
    haveI : Fact p.Prime := ⟨hp⟩
    have hpR : (p : R) ∈ IsLocalRing.maximalIdeal R := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
      exact CharP.cast_eq_zero _ p

    have hG1 : IsPGroup p ↥(lowerGroup R G 1) :=
      isPGroup_lowerGroup_one hpR iInf_maximalIdeal_pow_eq_bot

    obtain ⟨-, -, hcop'⟩ := exists_monoidHom_lowerGroup_zero_residueField_units (R := R) (G := G)
    have hcop := hcop' p hp hpR

    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
    have hcomm : ∀ s ∈ lowerGroup R G 0, ∀ t ∈ lowerGroup R G 0, Commute s t := by
      intro s _ t _
      obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg s)
      obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg t)
      exact Commute.zpow_zpow (Commute.refl g) a b
    have htame : ∀ j : ℕ, 1 ≤ j →
        lowerGroup R G j ≠ lowerGroup R G (j + 1) →
          (lowerGroup R G 1).relIndex (lowerGroup R G 0) ∣ j :=
      fun j hj hjump => relIndex_dvd_of_lowerGroup_ne_succ_of_commute hcomm hj hjump

    have hwild : ∀ σ ∈ lowerGroup R G 1, ∀ n : ℕ, 1 ≤ n → σ ^ p ^ n ≠ 1 →
        (ramificationDepth R G (σ ^ p ^ (n - 1))).toNat ≡
          (ramificationDepth R G (σ ^ p ^ n)).toNat [MOD p ^ n] :=
      fun σ hσ n hn hσn => ramificationDepth_pow_prime_pow_modEq_of_mem_lowerGroup_one hp hpR hσ hn hσn

    exact hasseArfChain_of_isCyclic_of_dvd_of_modEq hp hG1 hcop htame hwild

end

end

end Langlands.Ramification
