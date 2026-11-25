/-
Adapted from the Anthropic Lean formalisation of Fermat's Last Theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, files
`Theorems/Thm_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.lean`,
`P2M/Sol/S_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq.lean`,
`Theorems/Thm_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq.lean`,
`P2M/Sol/S_IsLocalRing_upperRamificationQuotientCompat_of_map_lowerRamificationGroup_mk_eq.lean`.
Copyright 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: the four files (two statements and their proofs) are merged and the helper lemmas
that both proofs had are kept once, in `Langlands.Ramification.RationalQuotient`; statements are on
the Library's `Langlands.Ramification.lowerGroup` and the rational Herbrand functions of
`Herbrand/Rational.lean`; names follow the Library; no options are set.
The paired Markdown file lists the changes.
-/

import Langlands.LocalFactor.Ramification.Herbrand.Rational
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Herbrand's tower law for the rational Herbrand functions

Let `H` be a normal subgroup of a finite group `G` acting on a local ring `R`, and let `G ⧸ H` act
on a local ring `S` (in the application, the invariants `FixedPoints.subring R H`). Assume the lower
groups of the quotient are the images of those of `G` in Herbrand's numbering:
`G_n H / H = (G/H)_⌈φ_H(n)⌉` for every `n`. Then the rational Herbrand functions satisfy the tower law
`φ_G = φ_{G/H} ∘ φ_H` on `u ≥ 0`, and the upper groups are compatible with the quotient:
`G^v H / H = (G/H)^v` for `v ≥ 0` (`UpperGroupRatQuotientCompat`). The hypothesis is Herbrand's
theorem, proved for discrete valuation rings in `Herbrand/LowerQuotient.lean`.
-/

namespace Langlands.Ramification

section

section

section

open IsLocalRing

namespace RationalQuotient

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

variable (R) in

noncomputable def herbrandPhiRatCeil (H : Type*) [Group H] [MulSemiringAction H R] (n : ℕ) : ℕ :=
  sInf {k : ℕ | herbrandPhiRat R H (n : ℚ) ≤ (k : ℚ)}

section HerbrandPhiCeil

variable {H : Type*} [Group H] [MulSemiringAction H R]

theorem herbrandPhiRatCeil_eq_ceil (n : ℕ) :
    herbrandPhiRatCeil R H n = ⌈herbrandPhiRat R H (n : ℚ)⌉₊ := by
  have hset : {k : ℕ | herbrandPhiRat R H (n : ℚ) ≤ (k : ℚ)} =
      Set.Ici ⌈herbrandPhiRat R H (n : ℚ)⌉₊ :=
    Set.ext fun k => by rw [Set.mem_ofPred_eq, Set.mem_Ici, Nat.ceil_le]
  show sInf {k : ℕ | herbrandPhiRat R H (n : ℚ) ≤ (k : ℚ)} = ⌈herbrandPhiRat R H (n : ℚ)⌉₊
  rw [hset, csInf_Ici]

@[scoped simp] theorem herbrandPhiRatCeil_zero : herbrandPhiRatCeil R H 0 = 0 := by
  rw [herbrandPhiRatCeil_eq_ceil, Nat.cast_zero, herbrandPhiRat_zero, Nat.ceil_zero]

end HerbrandPhiCeil

variable (R G) in

def LowerHerbrandQuotientCompat (S : Type*) [CommRing S] [IsLocalRing S]
    (H : Subgroup G) [H.Normal] [MulSemiringAction (G ⧸ H) S] : Prop :=
  ∀ n : ℕ,
    (lowerGroup R G n).map (QuotientGroup.mk' H) =
      lowerGroup S (G ⧸ H) (herbrandPhiRatCeil R H n)

variable (R G) in

def HerbrandPhiTowerCompat (S : Type*) [CommRing S] [IsLocalRing S]
    (H : Subgroup G) [H.Normal] [MulSemiringAction (G ⧸ H) S] : Prop :=
  ∀ u : ℚ, 0 ≤ u →
    herbrandPhiRat R G u = herbrandPhiRat S (G ⧸ H) (herbrandPhiRat R H u)

section TowerCompat

variable {S : Type*} [CommRing S] [IsLocalRing S]
variable {H : Subgroup G} [H.Normal] [MulSemiringAction (G ⧸ H) S]

theorem herbrandPhiRat_tower_zero :
    herbrandPhiRat R G (0 : ℚ) = herbrandPhiRat S (G ⧸ H) (herbrandPhiRat R H (0 : ℚ)) := by
  simp

namespace HerbrandPhiTowerCompat

theorem natCast (h : HerbrandPhiTowerCompat R G S H) (n : ℕ) :
    herbrandPhiRat R G (n : ℚ) = herbrandPhiRat S (G ⧸ H) (herbrandPhiRat R H (n : ℚ)) :=
  h n (Nat.cast_nonneg n)

end HerbrandPhiTowerCompat

end TowerCompat

theorem lowerGroupCard_dvd_of_le {i j : ℕ} (h : i ≤ j) :
    lowerGroupCard R G j ∣ lowerGroupCard R G i :=
  Subgroup.card_dvd_of_le ((lowerGroup_antitone _ _) h)

theorem lowerGroupCard_dvd_zero (i : ℕ) :
    lowerGroupCard R G i ∣ lowerGroupCard R G 0 :=
  lowerGroupCard_dvd_of_le (Nat.zero_le i)

theorem lowerGroupCard_dvd_sum_Icc (m : ℕ) :
    lowerGroupCard R G (m + 1) ∣
      ∑ i ∈ Finset.Icc 1 m, lowerGroupCard R G i :=
  Finset.dvd_sum fun _i hi =>
    lowerGroupCard_dvd_of_le ((Finset.mem_Icc.mp hi).2.trans (Nat.le_succ m))

theorem herbrandPhiRat_natCast_eq_cast_div (m : ℕ) :
    herbrandPhiRat R G m =
      ((∑ i ∈ Finset.Icc 1 m, lowerGroupCard R G i : ℕ) : ℚ) /
        (lowerGroupCard R G 0 : ℚ) := by
  rw [herbrandPhiRat_natCast, Nat.cast_sum]

theorem one_le_herbrandPhiRatCeil_succ [Finite G] (m : ℕ) :
    1 ≤ herbrandPhiRatCeil R G (m + 1) := by
  rw [herbrandPhiRatCeil_eq_ceil, Nat.one_le_ceil_iff]
  exact_mod_cast herbrandPhiRat_pos (R := R) (G := G)
    (Nat.cast_pos.mpr (Nat.succ_pos m))

theorem herbrandPhiRatCeil_succ_cast_sub_one_le [Finite G] (m : ℕ) :
    (herbrandPhiRatCeil R G (m + 1) : ℚ) - 1 ≤ herbrandPhiRat R G (m : ℚ) := by
  have hg0 : 0 < lowerGroupCard R G 0 := lowerGroupCard_pos 0
  have hg0' : (0 : ℚ) < (lowerGroupCard R G 0 : ℚ) := Nat.cast_pos.mpr hg0

  set h0 := lowerGroupCard R G 0 with hh0
  set hm1 := lowerGroupCard R G (m + 1) with hhm1
  set Sm := ∑ i ∈ Finset.Icc 1 m, lowerGroupCard R G i with hSm
  have hSm1 : ∑ i ∈ Finset.Icc 1 (m + 1), lowerGroupCard R G i = Sm + hm1 :=
    Finset.sum_Icc_succ_top (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero m)) _

  have hdvd0 : hm1 ∣ h0 := lowerGroupCard_dvd_zero (m + 1)
  have hdvdS : hm1 ∣ Sm := lowerGroupCard_dvd_sum_Icc m

  have hCeq : herbrandPhiRatCeil R G (m + 1) = ⌈((Sm + hm1 : ℕ) : ℚ) / (h0 : ℚ)⌉₊ := by
    rw [herbrandPhiRatCeil_eq_ceil, herbrandPhiRat_natCast_eq_cast_div, hSm1]
  set C := ⌈((Sm + hm1 : ℕ) : ℚ) / (h0 : ℚ)⌉₊ with hC

  have hNatIneq : C * h0 ≤ Sm + h0 := by

    have hCge : Sm + hm1 ≤ C * h0 := by
      have h1 : ((Sm + hm1 : ℕ) : ℚ) ≤ (C : ℚ) * h0 :=
        (div_le_iff₀ hg0').mp (Nat.le_ceil _)
      have h2 : ((Sm + hm1 : ℕ) : ℚ) ≤ ((C * h0 : ℕ) : ℚ) := by
        push_cast at h1 ⊢; linarith
      exact_mod_cast h2

    have hClt : C * h0 < Sm + hm1 + h0 := by
      have h1 : (C : ℚ) < ((Sm + hm1 : ℕ) : ℚ) / h0 + 1 :=
        Nat.ceil_lt_add_one (div_nonneg (Nat.cast_nonneg _) hg0'.le)
      have h2 : (C : ℚ) * h0 < ((Sm + hm1 : ℕ) : ℚ) + h0 := by
        have h3 := mul_lt_mul_of_pos_right h1 hg0'
        rw [add_one_mul, div_mul_cancel₀ _ hg0'.ne'] at h3; exact h3
      have h4 : ((C * h0 : ℕ) : ℚ) < ((Sm + hm1 + h0 : ℕ) : ℚ) := by
        push_cast at h2 ⊢; linarith
      exact_mod_cast h4

    have hdvd_diff : hm1 ∣ C * h0 - (Sm + hm1) :=
      Nat.dvd_sub (Dvd.dvd.mul_left hdvd0 C) (hdvdS.add (dvd_refl hm1))
    have hpos : 0 < h0 - (C * h0 - (Sm + hm1)) := by omega
    have hmle : hm1 ≤ h0 - (C * h0 - (Sm + hm1)) :=
      Nat.le_of_dvd hpos (Nat.dvd_sub hdvd0 hdvd_diff)
    omega

  rw [hCeq, herbrandPhiRat_natCast_eq_cast_div, ← hh0, ← hSm, le_div_iff₀ hg0']
  have hCast : (C : ℚ) * (h0 : ℚ) ≤ (Sm : ℚ) + (h0 : ℚ) := by
    have h := Nat.cast_le (α := ℚ).mpr hNatIneq; push_cast at h; linarith
  linarith

section Card

variable {S : Type*} [CommRing S] [IsLocalRing S]
variable {H : Subgroup G} [H.Normal] [MulSemiringAction (G ⧸ H) S]

theorem card_lowerGroup_map_mul_card_subgroup (n : ℕ) :
    Nat.card ((lowerGroup R G n).map (QuotientGroup.mk' H)) *
        lowerGroupCard R H n =
      lowerGroupCard R G n := by

  set Gn := lowerGroup R G n with hGn
  let f : Gn →* G ⧸ H := (QuotientGroup.mk' H).comp Gn.subtype

  have hrange : f.range = Gn.map (QuotientGroup.mk' H) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : f.ker = H.subgroupOf Gn := by
    rw [show f.ker = ((QuotientGroup.mk' H).ker).subgroupOf Gn from rfl,
      QuotientGroup.ker_mk']

  have hLagrange : Nat.card Gn = Nat.card f.range * Nat.card f.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker

  have hker_card : Nat.card f.ker = lowerGroupCard R H n := by
    have h1 : (f.ker).map Gn.subtype = H ⊓ Gn := by
      rw [hker, Subgroup.subgroupOf_map_subtype, inf_comm]
    have h2 := lowerGroup_map_subtype' (R := R) H n
    rw [← hGn] at h2
    calc Nat.card f.ker
        = Nat.card ((f.ker).map Gn.subtype) :=
          Nat.card_congr (Subgroup.equivMapOfInjective _ _ Gn.subtype_injective).toEquiv
      _ = Nat.card ((lowerGroup R H n).map H.subtype) := by rw [h1, h2]
      _ = lowerGroupCard R H n :=
          (Nat.card_congr
            (Subgroup.equivMapOfInjective _ _ H.subtype_injective).toEquiv).symm
  rw [show lowerGroupCard R G n = Nat.card Gn from rfl, hLagrange, hrange, hker_card]

theorem LowerHerbrandQuotientCompat.lowerGroupCard_quotient_mul
    (hc : LowerHerbrandQuotientCompat R G S H) (n : ℕ) :
    (lowerGroupCard S (G ⧸ H) (herbrandPhiRatCeil R H n) : ℚ) *
        (lowerGroupCard R H n : ℚ) =
      (lowerGroupCard R G n : ℚ) := by
  have h := card_lowerGroup_map_mul_card_subgroup (R := R) (G := G) (H := H) n
  have hcard :
      lowerGroupCard S (G ⧸ H) (herbrandPhiRatCeil R H n) =
        Nat.card ((lowerGroup R G n).map (QuotientGroup.mk' H)) := by
    unfold lowerGroupCard; rw [← hc n]
  rw [hcard]; exact_mod_cast h

end Card

section Tower

variable {S : Type*} [CommRing S] [IsLocalRing S]
variable {H : Subgroup G} [H.Normal] [MulSemiringAction (G ⧸ H) S]

variable [Finite G]

theorem herbrandPhiRat_mem_segment_phiCeil_succ (m : ℕ) :
    let j := herbrandPhiRatCeil R H (m + 1) - 1
    ((j : ℚ) ≤ herbrandPhiRat R H (m : ℚ) ∧ herbrandPhiRat R H (m : ℚ) ≤ (j : ℚ) + 1) ∧
      ((j : ℚ) ≤ herbrandPhiRat R H ((m : ℚ) + 1) ∧
        herbrandPhiRat R H ((m : ℚ) + 1) ≤ (j : ℚ) + 1) := by
  have h1 := one_le_herbrandPhiRatCeil_succ (R := R) (G := H) m
  have hcast : ((herbrandPhiRatCeil R H (m + 1) - 1 : ℕ) : ℚ) =
      (herbrandPhiRatCeil R H (m + 1) : ℚ) - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_one]
  have hkey := herbrandPhiRatCeil_succ_cast_sub_one_le (R := R) (G := H) m
  have hceil : herbrandPhiRat R H ((m : ℚ) + 1) ≤ (herbrandPhiRatCeil R H (m + 1) : ℚ) := by
    rw [herbrandPhiRatCeil_eq_ceil, show (m : ℚ) + 1 = ((m + 1 : ℕ) : ℚ) by push_cast; ring]
    exact Nat.le_ceil _
  have hmono : herbrandPhiRat R H (m : ℚ) ≤ herbrandPhiRat R H ((m : ℚ) + 1) :=
    herbrandPhiRat_monotone (by linarith)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hcast]; exact hkey
  · rw [hcast]; linarith
  · rw [hcast]; linarith
  · rw [hcast]; linarith

theorem LowerHerbrandQuotientCompat.herbrandPhiRat_comp_segment
    (hc : LowerHerbrandQuotientCompat R G S H) (m : ℕ) {u : ℚ}
    (hum : (m : ℚ) ≤ u) (hum1 : u ≤ (m : ℚ) + 1) :
    herbrandPhiRat S (G ⧸ H) (herbrandPhiRat R H u) -
        herbrandPhiRat S (G ⧸ H) (herbrandPhiRat R H (m : ℚ)) =
      (u - m) * (lowerGroupCard R G (m + 1) : ℚ) /
        (lowerGroupCard R G 0 : ℚ) := by
  obtain ⟨⟨ha1, ha2⟩, hb1, hb2⟩ :=
    herbrandPhiRat_mem_segment_phiCeil_succ (R := R) (G := G) (H := H) m
  set j := herbrandPhiRatCeil R H (m + 1) - 1 with hj
  have hj1 : j + 1 = herbrandPhiRatCeil R H (m + 1) :=
    Nat.sub_add_cancel (one_le_herbrandPhiRatCeil_succ (R := R) (G := H) m)

  have hHu_lo : (j : ℚ) ≤ herbrandPhiRat R H u := ha1.trans (herbrandPhiRat_monotone hum)
  have hHu_hi : herbrandPhiRat R H u ≤ (j : ℚ) + 1 := (herbrandPhiRat_monotone hum1).trans hb2

  have hchord :
      herbrandPhiRat S (G ⧸ H) (herbrandPhiRat R H u) -
          herbrandPhiRat S (G ⧸ H) (herbrandPhiRat R H (m : ℚ)) =
        (herbrandPhiRat R H u - herbrandPhiRat R H (m : ℚ)) *
          ((lowerGroupCard S (G ⧸ H) (herbrandPhiRatCeil R H (m + 1)) : ℚ) /
            (lowerGroupCard S (G ⧸ H) 0 : ℚ)) := by
    rw [herbrandPhiRat_segment j hHu_lo hHu_hi, herbrandPhiRat_segment j ha1 ha2, hj1]; ring

  have hHinc : herbrandPhiRat R H u - herbrandPhiRat R H (m : ℚ) =
      (u - m) *
        ((lowerGroupCard R H (m + 1) : ℚ) / (lowerGroupCard R H 0 : ℚ)) := by
    rw [herbrandPhiRat_segment m hum hum1]; ring
  rw [hchord, hHinc]

  have hcard0 := hc.lowerGroupCard_quotient_mul 0
  rw [herbrandPhiRatCeil_zero] at hcard0
  have hcardm1 := hc.lowerGroupCard_quotient_mul (m + 1)

  have hg0 : (lowerGroupCard R G 0 : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (lowerGroupCard_pos 0).ne'
  have hh0 : (lowerGroupCard R H 0 : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (lowerGroupCard_pos 0).ne'
  have hq0 : (lowerGroupCard S (G ⧸ H) 0 : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (lowerGroupCard_pos 0).ne'
  field_simp
  linear_combination (u - (m : ℚ)) * (lowerGroupCard R H 0 : ℚ) *
      (lowerGroupCard S (G ⧸ H) 0 : ℚ) * hcardm1 -
    (u - (m : ℚ)) * (lowerGroupCard R H (m + 1) : ℚ) *
      (lowerGroupCard S (G ⧸ H) (herbrandPhiRatCeil R H (m + 1)) : ℚ) * hcard0

theorem LowerHerbrandQuotientCompat.herbrandPhiRat_comp_natCast
    (hc : LowerHerbrandQuotientCompat R G S H) (n : ℕ) :
    herbrandPhiRat S (G ⧸ H) (herbrandPhiRat R H (n : ℚ)) = herbrandPhiRat R G (n : ℚ) := by
  induction n with
  | zero => simpa using (herbrandPhi_tower_zero (R := R) (G := G) (S := S) (H := H)).symm
  | succ m ih =>
    have hinc := hc.herbrandPhiRat_comp_segment m (u := (m : ℚ) + 1) (by linarith) le_rfl
    have hGseg := herbrandPhiRat_segment (R := R) (G := G) m
      (u := (m : ℚ) + 1) (by linarith) le_rfl
    push_cast
    linarith

theorem LowerHerbrandQuotientCompat.herbrandPhiRatTowerCompat
    (hc : LowerHerbrandQuotientCompat R G S H) :
    HerbrandPhiTowerCompat R G S H := by
  intro u hu
  set m := ⌊u⌋₊ with hm
  have hum : (m : ℚ) ≤ u := Nat.floor_le hu
  have hum1 : u ≤ (m : ℚ) + 1 := (Nat.lt_floor_add_one u).le
  have hGseg := herbrandPhiRat_segment (R := R) (G := G) m hum hum1
  have hinc := hc.herbrandPhiRat_comp_segment m hum hum1
  have hNat := hc.herbrandPhiRat_comp_natCast m
  linarith

end Tower

end RationalQuotient

end
open scoped RationalQuotient in

theorem herbrandPhiRat_eq_herbrandPhiRat_quotient_comp_of_map_lowerGroup_mk_eq
    {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R]
    {S : Type*} [CommRing S] [IsLocalRing S]
    {H : Subgroup G} [H.Normal] [MulSemiringAction (G ⧸ H) S]
    (hH : ∀ n : ℕ,
      (lowerGroup R G n).map (QuotientGroup.mk' H) =
        lowerGroup S (G ⧸ H) ⌈herbrandPhiRat R H (n : ℚ)⌉₊)
    {u : ℚ} (hu : 0 ≤ u) :
    herbrandPhiRat R G u =
      herbrandPhiRat S (G ⧸ H) (herbrandPhiRat R H u) := by
  have hc : RationalQuotient.LowerHerbrandQuotientCompat R G S H := fun n => by
    rw [RationalQuotient.herbrandPhiRatCeil_eq_ceil]
    exact hH n
  exact hc.herbrandPhiRatTowerCompat u hu

end

end

section

section
attribute [-simp] lowerGroup_subgroupOf lowerGroup_map_subtype

section

open IsLocalRing

namespace RationalQuotient

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

theorem sum_Icc_le_mul_of_herbrandPhiRat_natCast_le [Finite G] {m n : ℕ}
    (h : herbrandPhiRat R G m ≤ (n : ℚ)) :
    (∑ i ∈ Finset.Icc 1 m, lowerGroupCard R G i) ≤ n * lowerGroupCard R G 0 := by
  have hg0 : (0 : ℚ) < (lowerGroupCard R G 0 : ℚ) :=
    Nat.cast_pos.mpr (lowerGroupCard_pos (R := R) (G := G) 0)
  rw [herbrandPhiRat_natCast_eq_cast_div, div_le_iff₀ hg0] at h
  exact_mod_cast h

theorem exists_nat_segment_increment [Finite G] (m n : ℕ)
    (h : herbrandPhiRat R G m ≤ (n : ℚ)) :
    ∃ j : ℕ, ((n : ℚ) - herbrandPhiRat R G m) *
      (lowerGroupCard R G 0 : ℚ) / (lowerGroupCard R G (m + 1) : ℚ) = (j : ℚ) := by
  have hg0 : (0 : ℚ) < (lowerGroupCard R G 0 : ℚ) :=
    Nat.cast_pos.mpr (lowerGroupCard_pos (R := R) (G := G) 0)
  have hgm : (0 : ℚ) < (lowerGroupCard R G (m + 1) : ℚ) :=
    Nat.cast_pos.mpr (lowerGroupCard_pos (R := R) (G := G) (m + 1))

  have hle : (∑ i ∈ Finset.Icc 1 m, lowerGroupCard R G i) ≤
      n * lowerGroupCard R G 0 :=
    sum_Icc_le_mul_of_herbrandPhiRat_natCast_le h

  have hdvd : lowerGroupCard R G (m + 1) ∣
      n * lowerGroupCard R G 0 - ∑ i ∈ Finset.Icc 1 m, lowerGroupCard R G i :=
    Nat.dvd_sub ((lowerGroupCard_dvd_zero (m + 1)).mul_left n)
      (lowerGroupCard_dvd_sum_Icc m)
  obtain ⟨j, hj⟩ := hdvd
  refine ⟨j, ?_⟩

  have hnum : ((n : ℚ) - herbrandPhiRat R G m) * (lowerGroupCard R G 0 : ℚ) =
      ((n * lowerGroupCard R G 0 -
        ∑ i ∈ Finset.Icc 1 m, lowerGroupCard R G i : ℕ) : ℚ) := by
    rw [Nat.cast_sub hle, herbrandPhiRat_natCast_eq_cast_div, sub_mul,
      div_mul_cancel₀ _ hg0.ne', Nat.cast_mul]
  rw [hnum, hj, Nat.cast_mul, mul_div_cancel_left₀ _ hgm.ne']

theorem exists_nat_herbrandPsiRat_natCast [Finite G] (n : ℕ) :
    ∃ k : ℕ, herbrandPsiRat R G (n : ℚ) = (k : ℚ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, by rw [Nat.cast_zero]; exact herbrandPsiRat_zero⟩
  ·
    have hn' : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
    obtain ⟨m, hm⟩ : ∃ m, upperGroupRatIndex R G (n : ℚ) = m + 1 := by
      have h0 : upperGroupRatIndex R G (n : ℚ) ≠ 0 := by
        rw [Ne, upperGroupRatIndex_eq_zero_iff]
        exact not_le.mpr hn'
      exact ⟨upperGroupRatIndex R G (n : ℚ) - 1, by omega⟩
    obtain ⟨h1, h2⟩ := (upperGroupRatIndex_eq_succ_iff (R := R) (G := G)).mp hm
    obtain ⟨j, hj⟩ := exists_nat_segment_increment m n h1.le
    refine ⟨m + j, ?_⟩
    rw [herbrandPsiRat_segment m h1.le h2, hj, ← Nat.cast_add]

section Bridge

variable {S : Type*} [CommRing S] [IsLocalRing S]
variable {H : Subgroup G} [H.Normal] [MulSemiringAction (G ⧸ H) S]

theorem ceil_herbrandPhiRat_upperGroupRatIndex [Finite G]
    (htower : ∀ n : ℕ,
      herbrandPhiRat R G (n : ℚ) = herbrandPhiRat S (G ⧸ H) (herbrandPhiRat R H (n : ℚ)))
    (v : ℚ) :
    ⌈herbrandPhiRat R H (upperGroupRatIndex R G v : ℚ)⌉₊
      = upperGroupRatIndex S (G ⧸ H) v := by
  set n := upperGroupRatIndex R G v with hn_def
  set k := upperGroupRatIndex S (G ⧸ H) v with hk_def
  refine le_antisymm ?le_dir ?ge_dir
  case le_dir =>
    obtain ⟨m, hm⟩ := exists_nat_herbrandPsiRat_natCast (R := R) (G := H) k
    have hφm : herbrandPhiRat R H (m : ℚ) = (k : ℚ) := by
      have h := herbrandPhiRat_herbrandPsiRat (R := R) (G := H) (k : ℚ)
      rwa [hm] at h
    have hvm : v ≤ herbrandPhiRat R G (m : ℚ) := by
      rw [htower m, hφm]
      exact le_herbrandPhiRat_upperGroupRatIndex (R := S) (G := G ⧸ H) v
    have hnm : n ≤ m := upperGroupRatIndex_le (R := R) (G := G) hvm
    calc ⌈herbrandPhiRat R H (n : ℚ)⌉₊
        ≤ ⌈herbrandPhiRat R H (m : ℚ)⌉₊ :=
          Nat.ceil_le_ceil
            (herbrandPhiRat_monotone (R := R) (G := H) (Nat.cast_le.mpr hnm))
      _ = k := by rw [hφm, Nat.ceil_natCast]
  case ge_dir =>
    refine upperGroupRatIndex_le (R := S) (G := G ⧸ H) ?_
    calc v ≤ herbrandPhiRat R G (n : ℚ) :=
            le_herbrandPhiRat_upperGroupRatIndex (R := R) (G := G) v
      _ = herbrandPhiRat S (G ⧸ H) (herbrandPhiRat R H (n : ℚ)) := htower n
      _ ≤ herbrandPhiRat S (G ⧸ H) ((⌈herbrandPhiRat R H (n : ℚ)⌉₊ : ℕ) : ℚ) :=
            herbrandPhiRat_monotone (R := S) (G := G ⧸ H) (Nat.le_ceil _)

end Bridge

end RationalQuotient

end

theorem upperGroupRatQuotientCompat_of_map_lowerGroup_mk_eq
    {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R]
    {S : Type*} [CommRing S] [IsLocalRing S]
    {H : Subgroup G} [H.Normal] [MulSemiringAction (G ⧸ H) S]
    (hH : ∀ n : ℕ,
      (lowerGroup R G n).map (QuotientGroup.mk' H) =
        lowerGroup S (G ⧸ H) ⌈herbrandPhiRat R H (n : ℚ)⌉₊) :
    UpperGroupRatQuotientCompat R G S H := by

  have htower : ∀ n : ℕ, herbrandPhiRat R G (n : ℚ) =
      herbrandPhiRat S (G ⧸ H) (herbrandPhiRat R H (n : ℚ)) := fun n =>
    herbrandPhiRat_eq_herbrandPhiRat_quotient_comp_of_map_lowerGroup_mk_eq
      hH (Nat.cast_nonneg n)
  intro v _hv
  show (lowerGroup R G (upperGroupRatIndex R G v)).map
        (QuotientGroup.mk' H)
      = lowerGroup S (G ⧸ H)
          (upperGroupRatIndex S (G ⧸ H) v)
  rw [← RationalQuotient.ceil_herbrandPhiRat_upperGroupRatIndex htower v]
  exact hH (upperGroupRatIndex R G v)

end

end

end Langlands.Ramification
