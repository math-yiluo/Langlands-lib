/-
Adapted from the Anthropic Lean formalisation of Fermat's Last Theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, files
`Theorems/Thm_IsDiscreteValuationRing_relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute.lean`,
`P2M/Sol/S_IsDiscreteValuationRing_relIndex_dvd_of_lowerRamificationGroup_ne_succ_of_commute.lean`.
Copyright 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: the statement file and its proof are one module; the FLT proof name space
`P2MW.<file>.Ws45.HATame` is `Langlands.Ramification.HasseArf.Tame`, and the eight of its lemmas
that the FLT proof of the tame character also carried are those of `LowerGroupQuotients.lean`
(upstream's unit `uu` is `LowerGroupQuotients.unifUnit`); statements are on the Library's
`Langlands.Ramification.lowerGroup`; names follow the Library; no options are set.
The paired Markdown file lists the changes.
-/

import Langlands.LocalFactor.Ramification.LowerGroupQuotients

/-!
# Breaks of an abelian inertia group are divisible by the tame index

The tame part of the Hasse–Arf theorem. For a finite group acting on a discrete valuation ring
with perfect residue field, if the elements of `G_0` commute with one another, every break `i ≥ 1`
of the lower filtration (`G_i ≠ G_{i+1}`) is divisible by the tame index `[G_0 : G_1]`. For `τ` in
`G_i` but not in `G_{i+1}` and `s ∈ G_0`, comparing `(sτ)(ϖ)` with `(τs)(ϖ)` gives `θ₀(s)^i = 1`; as
`G_0/G_1` is cyclic and `θ₀` is injective on it, `[G_0 : G_1]` divides `i`.
-/

namespace Langlands.Ramification

section

section

section
namespace HasseArf.Tame

open IsLocalRing Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

theorem smul_sub_mem_maximalIdeal {s : G} (hs : s ∈ lowerGroup R G 0) (x : R) :
    s • x - x ∈ maximalIdeal R := by
  have h := (mem_lowerGroup.1 hs) x
  rwa [zero_add, pow_one] at h

theorem varpi_mem {ϖ : R} (hϖ : Irreducible ϖ) : ϖ ∈ maximalIdeal R := by
  rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ

theorem unifUnit_pow_sub_pow_mem {ϖ : R} (hϖ : Irreducible ϖ) {s : G} (hs : s ∈ lowerGroup R G 0) (n : ℕ) :
    (LowerGroupQuotients.unifUnit hϖ (s ^ n) : R) - (LowerGroupQuotients.unifUnit hϖ s : R) ^ n ∈ maximalIdeal R := by
  induction n with
  | zero => rw [pow_zero, pow_zero, LowerGroupQuotients.unifUnit_one, Units.val_one, sub_self]; exact zero_mem _
  | succ n ih =>
    have hcoc : (LowerGroupQuotients.unifUnit hϖ (s ^ n * s) : R) = (LowerGroupQuotients.unifUnit hϖ (s ^ n) : R) * ((s ^ n) • (LowerGroupQuotients.unifUnit hϖ s : R)) :=
      smul_uniformizer_unit_cocycle hϖ.ne_zero (LowerGroupQuotients.unifUnit_spec hϖ (s ^ n)) (LowerGroupQuotients.unifUnit_spec hϖ s) (LowerGroupQuotients.unifUnit_spec hϖ (s ^ n * s))
    have h1 : (s ^ n) • (LowerGroupQuotients.unifUnit hϖ s : R) - (LowerGroupQuotients.unifUnit hϖ s : R) ∈ maximalIdeal R :=
      smul_sub_mem_maximalIdeal ((lowerGroup R G 0).pow_mem hs n) _
    rw [pow_succ, hcoc]
    have hexp : (LowerGroupQuotients.unifUnit hϖ (s ^ n) : R) * ((s ^ n) • (LowerGroupQuotients.unifUnit hϖ s : R)) - (LowerGroupQuotients.unifUnit hϖ s : R) ^ (n + 1)
        = (LowerGroupQuotients.unifUnit hϖ (s ^ n) : R) * ((s ^ n) • (LowerGroupQuotients.unifUnit hϖ s : R) - (LowerGroupQuotients.unifUnit hϖ s : R))
          + ((LowerGroupQuotients.unifUnit hϖ (s ^ n) : R) - (LowerGroupQuotients.unifUnit hϖ s : R) ^ n) * (LowerGroupQuotients.unifUnit hϖ s : R) := by ring
    rw [hexp]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_right _ _ ih)

theorem pow_sub_one_mem_maximalIdeal_of_commute [Finite G] [PerfectField (ResidueField R)]
    {ϖ : R} (hϖ : Irreducible ϖ) {i : ℕ}
    {s τ : G} (hs : s ∈ lowerGroup R G 0)
    (hτ : τ ∈ lowerGroup R G i) (hτ' : τ ∉ lowerGroup R G (i + 1))
    (hc : Commute s τ) :
    (LowerGroupQuotients.unifUnit hϖ s : R) ^ i - 1 ∈ maximalIdeal R := by
  have hϖm : maximalIdeal R = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hu := LowerGroupQuotients.unifUnit_spec hϖ s
  have hv := LowerGroupQuotients.unifUnit_spec hϖ τ
  have hτ0 : τ ∈ lowerGroup R G 0 := lowerGroup_le_zero i hτ

  have hv1 : (LowerGroupQuotients.unifUnit hϖ τ : R) - 1 ∈ maximalIdeal R ^ i :=
    smul_uniformizer_unit_sub_one_mem_pow_of_mem_lowerGroup hϖm hϖ0 hv hτ
  rw [hϖm, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hv1
  obtain ⟨c, hcv⟩ := hv1
  have hcunit : c ∉ maximalIdeal R := by
    intro hcm
    apply hτ'
    refine mem_lowerGroup_of_smul_uniformizer_unit_sub_one_mem_pow (varpi_mem hϖ)
      (LowerGroupQuotients.smul_sub_dvd_smul_sub_of_mem_lowerGroup_zero hϖ hτ0) hv ?_
    rw [hϖm, Ideal.mem_span_singleton] at hcm
    obtain ⟨d, rfl⟩ := hcm
    rw [hϖm, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨d, by rw [← hcv]; ring⟩

  have hst : (s * τ) • ϖ = ((LowerGroupQuotients.unifUnit hϖ s : R) * (s • (LowerGroupQuotients.unifUnit hϖ τ : R))) * ϖ := by
    rw [mul_smul, hv, smul_mul', hu]; ring
  have hts : (τ * s) • ϖ = ((LowerGroupQuotients.unifUnit hϖ τ : R) * (τ • (LowerGroupQuotients.unifUnit hϖ s : R))) * ϖ := by
    rw [mul_smul, hu, smul_mul', hv]; ring
  have hcomm' : (LowerGroupQuotients.unifUnit hϖ s : R) * (s • (LowerGroupQuotients.unifUnit hϖ τ : R)) = (LowerGroupQuotients.unifUnit hϖ τ : R) * (τ • (LowerGroupQuotients.unifUnit hϖ s : R)) := by
    apply mul_right_cancel₀ hϖ0
    rw [← hst, ← hts, hc.eq]
  have h1 : τ • (LowerGroupQuotients.unifUnit hϖ s : R) - (LowerGroupQuotients.unifUnit hϖ s : R) ∈ maximalIdeal R ^ (i + 1) := (mem_lowerGroup.1 hτ) _
  have h2 : s • c - c ∈ maximalIdeal R := smul_sub_mem_maximalIdeal hs c
  have hsv : s • (LowerGroupQuotients.unifUnit hϖ τ : R) = 1 + (s • c) * (LowerGroupQuotients.unifUnit hϖ s : R) ^ i * ϖ ^ i := by
    have hveq : (LowerGroupQuotients.unifUnit hϖ τ : R) = 1 + c * ϖ ^ i := by rw [hcv]; ring
    rw [hveq, smul_add, smul_one, smul_mul', smul_pow', hu, mul_pow]
    ring
  have key : c * (LowerGroupQuotients.unifUnit hϖ s : R) * ϖ ^ i * ((LowerGroupQuotients.unifUnit hϖ s : R) ^ i - 1)
      = (LowerGroupQuotients.unifUnit hϖ τ : R) * (τ • (LowerGroupQuotients.unifUnit hϖ s : R) - (LowerGroupQuotients.unifUnit hϖ s : R)) - (s • c - c) * (LowerGroupQuotients.unifUnit hϖ s : R) ^ (i + 1) * ϖ ^ i := by
    rw [hsv] at hcomm'
    linear_combination hcomm' - (LowerGroupQuotients.unifUnit hϖ s : R) * hcv
  have hmem : c * (LowerGroupQuotients.unifUnit hϖ s : R) * ϖ ^ i * ((LowerGroupQuotients.unifUnit hϖ s : R) ^ i - 1) ∈ maximalIdeal R ^ (i + 1) := by
    rw [key]
    refine Ideal.sub_mem _ (Ideal.mul_mem_left _ _ h1) ?_
    rw [pow_succ']
    exact Ideal.mul_mem_mul (Ideal.mul_mem_right _ _ h2) (Ideal.pow_mem_pow (varpi_mem hϖ) i)

  rw [hϖm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  obtain ⟨d, hd⟩ := hmem
  have hmem' : c * ((LowerGroupQuotients.unifUnit hϖ s : R) * ((LowerGroupQuotients.unifUnit hϖ s : R) ^ i - 1)) ∈ maximalIdeal R := by
    rw [hϖm, Ideal.mem_span_singleton]
    refine ⟨d, mul_right_cancel₀ (pow_ne_zero i hϖ0) ?_⟩
    calc c * ((LowerGroupQuotients.unifUnit hϖ s : R) * ((LowerGroupQuotients.unifUnit hϖ s : R) ^ i - 1)) * ϖ ^ i
        = c * (LowerGroupQuotients.unifUnit hϖ s : R) * ϖ ^ i * ((LowerGroupQuotients.unifUnit hϖ s : R) ^ i - 1) := by ring
      _ = ϖ ^ (i + 1) * d := hd
      _ = ϖ * d * ϖ ^ i := by ring
  rcases (maximalIdeal.isMaximal R).isPrime.mem_or_mem hmem' with h | h
  · exact absurd h hcunit
  · rcases (maximalIdeal.isMaximal R).isPrime.mem_or_mem h with h' | h'
    · exact absurd h' (fun hm => (mem_nonunits_iff.1 ((mem_maximalIdeal _).1 hm)) (LowerGroupQuotients.unifUnit hϖ s).isUnit)
    · exact h'

end HasseArf.Tame
end

open IsLocalRing in
theorem relIndex_dvd_of_lowerGroup_ne_succ_of_commute
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R]
    [PerfectField (IsLocalRing.ResidueField R)]
    (hcomm : ∀ s ∈ lowerGroup R G 0,
      ∀ t ∈ lowerGroup R G 0, Commute s t)
    {i : ℕ} (hi : 1 ≤ i)
    (hjump : lowerGroup R G i ≠ lowerGroup R G (i + 1)) :
    (lowerGroup R G 1).relIndex (lowerGroup R G 0) ∣ i := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R

  have hle : lowerGroup R G (i + 1) ≤ lowerGroup R G i :=
    (lowerGroup_antitone _ _) (Nat.le_succ i)
  obtain ⟨τ, hτ, hτ'⟩ : ∃ τ ∈ lowerGroup R G i, τ ∉ lowerGroup R G (i + 1) := by
    by_contra h
    apply hjump
    refine le_antisymm (fun x hx => ?_) hle
    by_contra hx'
    exact h ⟨x, hx, hx'⟩
  have hτ0 : τ ∈ lowerGroup R G 0 := lowerGroup_le_zero i hτ

  have hpow : ∀ s ∈ lowerGroup R G 0, (LowerGroupQuotients.unifUnit hϖ s : R) ^ i - 1 ∈ maximalIdeal R :=
    fun s hs => HasseArf.Tame.pow_sub_one_mem_maximalIdeal_of_commute hϖ hs hτ hτ' (hcomm s hs τ hτ0)

  obtain ⟨-, hcyc, -⟩ :=
    exists_monoidHom_lowerGroup_zero_residueField_units (R := R) (G := G)
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  obtain ⟨g0, rfl⟩ := QuotientGroup.mk_surjective g

  have hgi : ((g0 : G) ^ i) ∈ lowerGroup R G 1 := by
    have hmod := HasseArf.Tame.unifUnit_pow_sub_pow_mem hϖ g0.2 i
    have h1 : (LowerGroupQuotients.unifUnit hϖ ((g0 : G) ^ i) : R) - 1 ∈ maximalIdeal R ^ 1 := by
      rw [pow_one]
      have := Ideal.add_mem _ hmod (hpow (g0 : G) g0.2)
      rwa [sub_add_sub_cancel] at this
    exact mem_lowerGroup_of_smul_uniformizer_unit_sub_one_mem_pow (HasseArf.Tame.varpi_mem hϖ)
      (LowerGroupQuotients.smul_sub_dvd_smul_sub_of_mem_lowerGroup_zero hϖ ((lowerGroup R G 0).pow_mem g0.2 i)) (LowerGroupQuotients.unifUnit_spec hϖ _) h1
  have hone : (QuotientGroup.mk g0 : ↥(lowerGroup R G 0) ⧸
      (lowerGroup R G 1).subgroupOf (lowerGroup R G 0)) ^ i = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    exact hgi
  have hord := orderOf_eq_card_of_forall_mem_zpowers hg
  show Nat.card (↥(lowerGroup R G 0) ⧸
      (lowerGroup R G 1).subgroupOf (lowerGroup R G 0)) ∣ i
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one hone

end

end

end Langlands.Ramification
