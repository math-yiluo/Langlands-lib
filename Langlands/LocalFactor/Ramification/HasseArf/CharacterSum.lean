/-
Adapted from the Anthropic Lean formalisation of Fermat's Last Theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, files
`Theorems/Thm_IsDiscreteValuationRing_finsum_lowerRamificationGroup_indicator_comp_mk_eq.lean`,
`P2M/Sol/S_IsDiscreteValuationRing_finsum_lowerRamificationGroup_indicator_comp_mk_eq.lean`,
`Theorems/Thm_IsDiscreteValuationRing_exists_finsum_lowerRamificationGroup_indicator_eq_natCast.lean`,
`P2M/Sol/S_IsDiscreteValuationRing_exists_finsum_lowerRamificationGroup_indicator_eq_natCast.lean`.
Copyright 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: the four files (two statements and their proofs) are one module; the FLT proof name
space `P2MW.<file>.IsLocalRing.SwanInfl`, which both proofs carried, is kept once as
`Langlands.Ramification.HasseArf.CharacterSum`; statements are on the Library's
`Langlands.Ramification.lowerGroup`; names follow the Library; no options are set.
The paired Markdown file lists the changes.
-/

import Langlands.LocalFactor.Ramification.FixedSubringQuotient
import Langlands.LocalFactor.Ramification.HasseArf.Cyclic
import Langlands.LocalFactor.Ramification.Herbrand.LowerQuotient
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Basic.Complex.Basic

/-!
# Integrality of the lower-group sum of a character

For a finite group acting on a discrete valuation ring and a character `ψ` of the group, the sum
`∑_i |G_{i+1}|/|G_0| · [ψ is not trivial on G_{i+1}]` (the exponent of the Swan conductor of `ψ`) is
the value `φ(d - 1)` of the Herbrand function, `d` the first index at which `ψ` is trivial on `G_d`.
It is unchanged when computed for the quotient by a normal subgroup on which the character factors,
and, by the Hasse–Arf theorem for the cyclic quotient `G ⧸ ker ψ`, it is a natural number.
-/

namespace Langlands.Ramification

section

section
attribute [-simp] lowerGroup_subgroupOf lowerGroup_map_subtype

section
open IsLocalRing (maximalIdeal maximalIdeal.isMaximal residue)
namespace HasseArf.CharacterSum
open IsLocalRing

open IsLocalRing

section generic

variable {R : Type*} [CommRing R] [IsLocalRing R] {Γ : Type*} [Group Γ] [Finite Γ] [MulSemiringAction Γ R]
  {A : Type*} [CommGroup A] (χ : Γ →* A)

def Triv (n : ℕ) : Prop := ∀ σ ∈ lowerGroup R Γ n, χ σ = 1

omit [Finite Γ] in
theorem Triv.mono {χ : Γ →* A} {m n : ℕ} (hmn : m ≤ n) (hm : Triv (R := R) χ m) : Triv (R := R) χ n :=
  fun σ hσ => hm σ ((lowerGroup_antitone _ _) hmn hσ)

variable (R) in

noncomputable def firstTriv (h : ∃ N, Triv (R := R) χ N) : ℕ := by classical exact Nat.find h

omit [Finite Γ] in
theorem triv_iff_firstTriv_le (h : ∃ N, Triv (R := R) χ N) (n : ℕ) : Triv (R := R) χ n ↔ firstTriv R χ h ≤ n := by
  classical
  constructor
  · intro hn; exact Nat.find_min' h hn
  · intro hn; exact (Nat.find_spec h).mono hn

open scoped Classical in

theorem finsum_indicator_eq_herbrandPhiRat (h : ∃ N, Triv (R := R) χ N) :
    ∑ᶠ i : ℕ, (Nat.card (lowerGroup R Γ (i + 1)) : ℚ) / (Nat.card (lowerGroup R Γ 0) : ℚ) *
        (if Triv (R := R) χ (i + 1) then 0 else 1) =
      herbrandPhiRat R Γ ((firstTriv R χ h - 1 : ℕ) : ℚ) := by
  classical
  set d := firstTriv R χ h with hd
  have hiff : ∀ n, Triv (R := R) χ n ↔ d ≤ n := triv_iff_firstTriv_le χ h

  let t : ℕ → ℚ := fun i => (Nat.card (lowerGroup R Γ (i + 1)) : ℚ) /
      (Nat.card (lowerGroup R Γ 0) : ℚ) * (if Triv (R := R) χ (i + 1) then 0 else 1)
  have ht_out : ∀ i, ¬ i + 1 < d → t i = 0 := fun i hi => by
    simp only [t, ite_eq_left ((hiff (i + 1)).mpr (by omega)), mul_zero]
  have ht_in : ∀ i, i + 1 < d → t i = (lowerGroupCard R Γ (i + 1) : ℚ) / (lowerGroupCard R Γ 0 : ℚ) := fun i hi => by
    simp only [t, ite_eq_right ((hiff (i + 1)).not.mpr (by omega)), mul_one]
    rfl
  change ∑ᶠ i, t i = _
  rw [finsum_eq_sum_of_support_subset t (s := Finset.range (d - 1)) (by
      intro i hi
      rw [Function.mem_support] at hi
      rw [Finset.mem_coe, Finset.mem_range]
      by_contra hni
      exact hi (ht_out i (by omega)))]
  rw [Finset.sum_congr rfl (fun i hi => ht_in i (by rw [Finset.mem_range] at hi; omega)), herbrandPhiRat_natCast,
    ← Finset.sum_div]
  congr 1
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · rw [hd0]
    simp
  · have hIcc : Finset.Icc 1 (d - 1) = Finset.Ico 1 d := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIcc, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [add_comm]

theorem upperGroupRatIndex_pos {v : ℚ} (hv : 0 < v) : 0 < upperGroupRatIndex R Γ v := by
  by_contra h0
  have h0' : upperGroupRatIndex R Γ v = 0 := by omega
  have := le_herbrandPhiRat_upperGroupRatIndex (R := R) (G := Γ) v
  rw [h0', Nat.cast_zero, herbrandPhiRat_zero] at this
  exact absurd this (not_le.mpr hv)

theorem not_triv_upper_iff (h : ∃ N, Triv (R := R) χ N) {v : ℚ} (hv : 0 < v) :
    (¬ ∀ σ ∈ upperGroupRat R Γ v, χ σ = 1) ↔ v ≤ herbrandPhiRat R Γ ((firstTriv R χ h - 1 : ℕ) : ℚ) := by
  set d := firstTriv R χ h with hd
  have hiff : ∀ n, Triv (R := R) χ n ↔ d ≤ n := triv_iff_firstTriv_le χ h
  change ¬ Triv (R := R) χ (upperGroupRatIndex R Γ v) ↔ _
  rw [(hiff _).not, not_le]
  have hpos := upperGroupRatIndex_pos (R := R) (Γ := Γ) hv
  constructor
  · intro hlt

    refine (le_herbrandPhiRat_upperGroupRatIndex (R := R) (G := Γ) v).trans ?_
    exact (herbrandPhiRat_monotone (R := R) (G := Γ)) (by exact_mod_cast (show upperGroupRatIndex R Γ v ≤ d - 1 by omega))
  · intro hle
    have := upperGroupRatIndex_le (R := R) (G := Γ) hle
    omega

end generic

end HasseArf.CharacterSum
end

section
open IsLocalRing (maximalIdeal maximalIdeal.isMaximal residue)
namespace HasseArf.CharacterSum
open IsLocalRing

open IsLocalRing

section aux

theorem exists_index_eq_bot_of_antitone_of_iInf_eq_bot {G : Type*} [Group G] [Finite G] (f : ℕ → Subgroup G) (hf : Antitone f)
    (h : ⨅ i, f i = ⊥) : ∃ N, f N = ⊥ := by
  classical
  haveI : Finite (Subgroup G) := inferInstance
  obtain ⟨s, hs⟩ := (Set.toFinite (Set.range f)).exists_finset_coe

  have hidx : ∀ K ∈ s, ∃ n, f n = K := fun K hK => by
    have : K ∈ Set.range f := by rw [← hs]; exact hK
    exact this
  choose! idx hidx' using hidx
  refine ⟨s.sup idx, le_bot_iff.mp ?_⟩
  rw [← h]
  refine le_iInf fun m => ?_
  have hm : f m ∈ s := by rw [← Finset.mem_coe, hs]; exact ⟨m, rfl⟩
  rw [← hidx' (f m) hm]
  exact hf (Finset.le_sup hm)

theorem eq_of_forall_pos_le_iff {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : ∀ v : ℚ, 0 < v → (v ≤ a ↔ v ≤ b)) : a = b := by
  apply le_antisymm
  · rcases eq_or_lt_of_le ha with rfl | ha'
    · exact hb
    · exact (h a ha').mp le_rfl
  · rcases eq_or_lt_of_le hb with rfl | hb'
    · exact ha
    · exact (h b hb').mpr le_rfl

end aux

end HasseArf.CharacterSum
end

open IsLocalRing HasseArf.CharacterSum in
open scoped Classical in

theorem finsum_lowerGroup_indicator_comp_mk_eq
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    (H : Subgroup G) [H.Normal] {A : Type*} [CommGroup A] (χ : G ⧸ H →* A) :
    ∑ᶠ i : ℕ,
        (Nat.card (lowerGroup R G (i + 1)) : ℚ) /
            (Nat.card (lowerGroup R G 0) : ℚ) *
          (if ∀ σ ∈ lowerGroup R G (i + 1), χ (QuotientGroup.mk σ) = 1 then 0 else 1) =
      ∑ᶠ j : ℕ,
        (Nat.card (lowerGroup (FixedPoints.subring R H) (G ⧸ H) (j + 1)) : ℚ) /
            (Nat.card (lowerGroup (FixedPoints.subring R H) (G ⧸ H) 0) : ℚ) *
          (if ∀ τ ∈ lowerGroup (FixedPoints.subring R H) (G ⧸ H) (j + 1), χ τ = 1
            then 0 else 1) := by
  classical

  have hsep : ⨅ n, (maximalIdeal R) ^ n = ⊥ := Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top
  obtain ⟨N, hN⟩ := HasseArf.CharacterSum.exists_index_eq_bot_of_antitone_of_iInf_eq_bot (lowerGroup R G) (lowerGroup_antitone _ _)
    (iInf_lowerGroup_eq_bot hsep)
  have h1 : ∃ N, HasseArf.CharacterSum.Triv (R := R) (χ.comp (QuotientGroup.mk' H)) N :=
    ⟨N, fun σ hσ => by rw [hN, Subgroup.mem_bot] at hσ; rw [hσ, map_one]⟩

  have hH := map_lowerGroup_mk_eq_of_isSeparable_residueField (R := R) (G := G) (H := H) N
  rw [hN, Subgroup.map_bot] at hH
  have h2 : ∃ N', HasseArf.CharacterSum.Triv (R := FixedPoints.subring R H) χ N' :=
    ⟨_, fun τ hτ => by rw [← hH, Subgroup.mem_bot] at hτ; rw [hτ, map_one]⟩

  refine (HasseArf.CharacterSum.finsum_indicator_eq_herbrandPhiRat (χ.comp (QuotientGroup.mk' H)) h1).trans
    (Eq.trans ?_ (HasseArf.CharacterSum.finsum_indicator_eq_herbrandPhiRat χ h2).symm)

  have hC := upperGroupRatQuotientCompat_of_isSeparable_residueField (R := R) (G := G) H
  refine HasseArf.CharacterSum.eq_of_forall_pos_le_iff (herbrandPhiRat_nonneg (Nat.cast_nonneg _)) (herbrandPhiRat_nonneg (Nat.cast_nonneg _)) (fun v hv => ?_)
  rw [← HasseArf.CharacterSum.not_triv_upper_iff (χ.comp (QuotientGroup.mk' H)) h1 hv, ← HasseArf.CharacterSum.not_triv_upper_iff χ h2 hv, ← hC v hv.le]
  refine not_congr ⟨fun hG τ hτ => ?_, fun hQ σ hσ => hQ _ (Subgroup.mem_map_of_mem _ hσ)⟩
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hτ
  exact hG σ hσ

end

end

section

section
attribute [-simp] lowerGroup_subgroupOf lowerGroup_map_subtype

section
open IsLocalRing (ResidueField maximalIdeal maximalIdeal.isMaximal residue)
namespace HasseArf.CharacterSum
open IsLocalRing

open IsLocalRing

section generic

variable {R : Type*} [CommRing R] [IsLocalRing R] {Γ : Type*} [Group Γ] [Finite Γ] [MulSemiringAction Γ R]
  {A : Type*} [CommGroup A] (χ : Γ →* A)

end generic

end HasseArf.CharacterSum
end

section
open IsLocalRing (ResidueField maximalIdeal maximalIdeal.isMaximal residue)
namespace HasseArf.CharacterSum
open IsLocalRing

open IsLocalRing

theorem exists_index_lowerGroup_eq_bot {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    {Γ : Type*} [Group Γ] [Finite Γ] [MulSemiringAction Γ S] [FaithfulSMul Γ S] :
    ∃ N, lowerGroup S Γ N = ⊥ := by
  have hsep : ⨅ n, (IsLocalRing.maximalIdeal S) ^ n = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal S).ne_top
  exact exists_index_eq_bot_of_antitone_of_iInf_eq_bot (lowerGroup S Γ) (lowerGroup_antitone _ _)
    (iInf_lowerGroup_eq_bot hsep)

end HasseArf.CharacterSum
end

open IsLocalRing in
open HasseArf.CharacterSum in
open scoped Classical in

theorem exists_finsum_lowerGroup_indicator_eq_natCast
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    [PerfectField (IsLocalRing.ResidueField R)]
    (ψ : G →* ℂˣ) :
    ∃ m : ℕ,
      ∑ᶠ i : ℕ,
        (Nat.card (lowerGroup R G (i + 1)) : ℚ) /
            (Nat.card (lowerGroup R G 0) : ℚ) *
          (if ∀ σ ∈ lowerGroup R G (i + 1), ψ σ = 1 then 0 else 1) = m := by

  have hA := finsum_lowerGroup_indicator_comp_mk_eq (R := R) (G := G) ψ.ker (QuotientGroup.kerLift ψ)
  have e1 : (∑ᶠ i : ℕ,
        (Nat.card (lowerGroup R G (i + 1)) : ℚ) /
            (Nat.card (lowerGroup R G 0) : ℚ) *
          (if ∀ σ ∈ lowerGroup R G (i + 1), ψ σ = 1 then 0 else 1)) =
      ∑ᶠ j : ℕ,
        (Nat.card (lowerGroup (FixedPoints.subring R ψ.ker) (G ⧸ ψ.ker) (j + 1)) : ℚ) /
            (Nat.card (lowerGroup (FixedPoints.subring R ψ.ker) (G ⧸ ψ.ker) 0) : ℚ) *
          (if ∀ τ ∈ lowerGroup (FixedPoints.subring R ψ.ker) (G ⧸ ψ.ker) (j + 1), QuotientGroup.kerLift ψ τ = 1
            then 0 else 1) := by
    refine Eq.trans (finsum_congr fun i => congrArg₂ (· * ·) rfl (@if_congr ℚ _ _ (_) (_) _ _ _ _ ?_ rfl rfl)) hA
    exact forall₂_congr fun σ _ => by rw [QuotientGroup.kerLift_mk]
  rw [e1]

  haveI : IsDiscreteValuationRing (FixedPoints.subring R ψ.ker) := isDiscreteValuationRing_fixedSubring
  obtain ⟨hfaith, hperf, hlies, hsep⟩ :=
    faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_fixedSubring (R := R) (G := G) ψ.ker
  haveI := hfaith
  haveI := hperf
  haveI := hlies
  haveI := hsep
  haveI : IsCyclic (G ⧸ ψ.ker) :=
    isCyclic_of_injective_ringHom ((Units.coeHom ℂ).comp (QuotientGroup.kerLift ψ))
      (fun a b h => QuotientGroup.kerLift_injective ψ (Units.ext h))
  have hHA := hasseArfChain_lowerGroup_of_isCyclic (R := FixedPoints.subring R ψ.ker) (G := G ⧸ ψ.ker)

  have hinj := QuotientGroup.kerLift_injective ψ
  have htriv : ∀ n, HasseArf.CharacterSum.Triv (R := FixedPoints.subring R ψ.ker) (QuotientGroup.kerLift ψ) n ↔
      lowerGroup (FixedPoints.subring R ψ.ker) (G ⧸ ψ.ker) n = ⊥ := fun n => by
    rw [Subgroup.eq_bot_iff_forall]
    refine forall₂_congr fun τ _ => ⟨fun h => hinj (by rw [h, map_one]), fun h => by rw [h, map_one]⟩
  obtain ⟨N, hN⟩ := HasseArf.CharacterSum.exists_index_lowerGroup_eq_bot (S := FixedPoints.subring R ψ.ker) (Γ := G ⧸ ψ.ker)
  have hfin : ∃ N, HasseArf.CharacterSum.Triv (R := FixedPoints.subring R ψ.ker) (QuotientGroup.kerLift ψ) N := ⟨N, (htriv N).2 hN⟩
  have e2 := HasseArf.CharacterSum.finsum_indicator_eq_herbrandPhiRat (QuotientGroup.kerLift ψ) hfin
  unfold HasseArf.CharacterSum.Triv at e2
  rw [e2]
  set d := HasseArf.CharacterSum.firstTriv (FixedPoints.subring R ψ.ker) (QuotientGroup.kerLift ψ) hfin with hd
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · refine ⟨0, ?_⟩
    rw [hd0]
    simp
  ·
    have hjump : lowerGroup (FixedPoints.subring R ψ.ker) (G ⧸ ψ.ker) (d - 1) ≠
        lowerGroup (FixedPoints.subring R ψ.ker) (G ⧸ ψ.ker) (d - 1 + 1) := by
      rw [Nat.sub_add_cancel hdpos]
      intro h
      have h1 : ¬ HasseArf.CharacterSum.Triv (R := FixedPoints.subring R ψ.ker) (QuotientGroup.kerLift ψ) (d - 1) :=
        fun ht => by have := (HasseArf.CharacterSum.triv_iff_firstTriv_le _ hfin (d - 1)).1 ht; omega
      have h2 : HasseArf.CharacterSum.Triv (R := FixedPoints.subring R ψ.ker) (QuotientGroup.kerLift ψ) d := (HasseArf.CharacterSum.triv_iff_firstTriv_le _ hfin d).2 le_rfl
      exact h1 ((htriv _).2 (h.trans ((htriv _).1 h2)))
    obtain ⟨m, hm⟩ := hHA (d - 1) hjump
    refine ⟨m, ?_⟩
    rw [herbrandPhiRat_natCast]
    unfold lowerGroupCard
    have h0 : (Nat.card (lowerGroup (FixedPoints.subring R ψ.ker) (G ⧸ ψ.ker) 0) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.2 (lowerGroupCard_pos (R := FixedPoints.subring R ψ.ker) (G := G ⧸ ψ.ker) 0).ne'
    rw [div_eq_iff h0]
    exact_mod_cast (by rw [hm, mul_comm] : (∑ j ∈ Finset.Icc 1 (d - 1), Nat.card (lowerGroup (FixedPoints.subring R ψ.ker) (G ⧸ ψ.ker) j)) = m * Nat.card (lowerGroup (FixedPoints.subring R ψ.ker) (G ⧸ ψ.ker) 0))

end

end

end Langlands.Ramification
