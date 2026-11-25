/-
Adapted from the Anthropic Lean formalisation of Fermat's Last Theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, files
`Definitions/Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup.lean`,
`Definitions/Def_Mathlib_RingTheory_Valuation_UpperRamificationGroupPsi.lean`.
Copyright 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: the two files are merged; statements are on the Library's
`Langlands.Ramification.lowerGroup`; names follow the Library, with the rational functions named
`herbrandPhiRat`, `herbrandPsiRat`, `upperGroupRat` beside the Library's real `Padic.herbrandPhi`,
`Padic.herbrandPsi`, `Padic.upperRamificationGroup`; the `ValuationSubring` versions, the example
blocks and the in-file checks are not kept; no options are set, and the raised heartbeat limit of
`herbrandPhi_strictMono` is not needed.
The paired Markdown file lists the changes.
-/

import Langlands.LocalFactor.Ramification.LowerGroup
import Mathlib.Data.Rat.Floor

/-!
# The Herbrand functions on the rationals and upper groups with rational index

For a finite group acting on a local ring, with `g_i = |G_i|` (`lowerGroupCard`), the Herbrand
function on the rationals is the piecewise linear function
`φ(u) = (g_1 + ⋯ + g_⌊u⌋ + (u - ⌊u⌋) g_{⌊u⌋+1}) / g_0` for `u > 0` and `φ(u) = u` for `u ≤ 0`
(`herbrandPhiRat`). It is a strictly increasing bijection of `ℚ`; `herbrandPsiRat` is its
inverse. The upper group `G^v` is the lower group `G_n` for the least `n` with `v ≤ φ(n)`
(`upperGroupRat`, `upperGroupRatIndex`), which is `G_⌈ψ(v)⌉`. These rational functions are the
auxiliary ones of the FLT development; the Library's Herbrand functions on the reals for finite
p-adic extensions are `Padic.herbrandPhi`, `Padic.herbrandPsi` (`Herbrand/Finite.lean`), and
`Herbrand/LocalQuotientProof.lean` and `Herbrand/QuotientProof.lean` compare the two.
-/

namespace Langlands.Ramification

section

section
open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

variable (R G) in

noncomputable def lowerGroupCard (i : ℕ) : ℕ :=
  Nat.card (lowerGroup R G i)

theorem lowerGroupCard_pos [Finite G] (i : ℕ) :
    0 < lowerGroupCard R G i := by
  haveI : Nonempty (lowerGroup R G i) := ⟨⟨1, Subgroup.one_mem _⟩⟩
  exact Nat.card_pos

theorem one_le_lowerGroupCard_cast [Finite G] (i : ℕ) :
    (1 : ℚ) ≤ (lowerGroupCard R G i : ℚ) :=
  Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr (lowerGroupCard_pos i).ne')

theorem lowerGroupCard_of_subsingleton [Subsingleton G] (i : ℕ) :
    lowerGroupCard R G i = 1 := by
  haveI : Nonempty (lowerGroup R G i) := ⟨⟨1, Subgroup.one_mem _⟩⟩
  haveI : Subsingleton (lowerGroup R G i) :=
    ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  exact Nat.card_unique

variable (R G) in

noncomputable def herbrandPhiRat (u : ℚ) : ℚ :=
  if u ≤ 0 then u
  else ((∑ i ∈ Finset.Icc 1 ⌊u⌋₊, (lowerGroupCard R G i : ℚ)) +
      (u - ⌊u⌋₊) * lowerGroupCard R G (⌊u⌋₊ + 1)) / lowerGroupCard R G 0

theorem herbrandPhiRat_of_nonpos {u : ℚ} (h : u ≤ 0) : herbrandPhiRat R G u = u := ite_eq_left h

@[simp] theorem herbrandPhiRat_zero : herbrandPhiRat R G 0 = 0 := herbrandPhiRat_of_nonpos le_rfl

theorem herbrandPhiRat_of_pos {u : ℚ} (h : 0 < u) :
    herbrandPhiRat R G u =
      ((∑ i ∈ Finset.Icc 1 ⌊u⌋₊, (lowerGroupCard R G i : ℚ)) +
        (u - ⌊u⌋₊) * lowerGroupCard R G (⌊u⌋₊ + 1)) / lowerGroupCard R G 0 :=
  ite_eq_right (not_le.mpr h)

theorem herbrandPhiRat_natCast (n : ℕ) :
    herbrandPhiRat R G n =
      (∑ i ∈ Finset.Icc 1 n, (lowerGroupCard R G i : ℚ)) / lowerGroupCard R G 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) from Finset.Icc_eq_empty (by omega),
      Finset.sum_empty, zero_div, Nat.cast_zero, herbrandPhiRat_zero]
  · have hpos : (0 : ℚ) < n := Nat.cast_pos.mpr hn
    rw [herbrandPhiRat_of_pos hpos, Nat.floor_natCast, sub_self, zero_mul, add_zero]

theorem herbrandPhiRat_nonneg {u : ℚ} (h : 0 ≤ u) : 0 ≤ herbrandPhiRat R G u := by
  rcases eq_or_lt_of_le h with rfl | hu
  · simp
  · rw [herbrandPhiRat_of_pos hu]
    have h1 : (0 : ℚ) ≤ u - ⌊u⌋₊ := sub_nonneg.mpr (Nat.floor_le hu.le)
    have h2 : (0 : ℚ) ≤ ∑ i ∈ Finset.Icc 1 ⌊u⌋₊, (lowerGroupCard R G i : ℚ) :=
      Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
    exact div_nonneg (add_nonneg h2 (mul_nonneg h1 (Nat.cast_nonneg _))) (Nat.cast_nonneg _)

theorem herbrandPhiRat_pos [Finite G] {v : ℚ} (hv : 0 < v) : 0 < herbrandPhiRat R G v := by
  rw [herbrandPhiRat_of_pos hv]
  refine div_pos ?_ (Nat.cast_pos.mpr (lowerGroupCard_pos (R := R) (G := G) 0))
  rcases Nat.eq_zero_or_pos ⌊v⌋₊ with h0 | h0
  · rw [h0, show Finset.Icc 1 0 = (∅ : Finset ℕ) from Finset.Icc_eq_empty (by omega),
      Finset.sum_empty, Nat.cast_zero, sub_zero]
    simpa using mul_pos hv
      (Nat.cast_pos.mpr (lowerGroupCard_pos (R := R) (G := G) 1) : (0 : ℚ) < _)
  · refine add_pos_of_pos_of_nonneg
      (Finset.sum_pos (fun i _ => ?_) ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, h0⟩⟩) ?_
    · exact Nat.cast_pos.mpr (lowerGroupCard_pos i)
    · exact mul_nonneg (sub_nonneg.mpr (Nat.floor_le hv.le)) (Nat.cast_nonneg _)

theorem herbrandPhiRat_strictMono [Finite G] : StrictMono (herbrandPhiRat R G) := by
  intro u v huv
  by_cases hv : v ≤ 0
  · rw [herbrandPhiRat_of_nonpos (huv.le.trans hv), herbrandPhiRat_of_nonpos hv]
    exact huv
  rw [not_le] at hv
  by_cases hu : u ≤ 0
  · rw [herbrandPhiRat_of_nonpos hu]
    exact hu.trans_lt (herbrandPhiRat_pos hv)
  · rw [not_le] at hu
    rw [herbrandPhiRat_of_pos hu, herbrandPhiRat_of_pos hv, div_eq_mul_inv, div_eq_mul_inv]
    have hg0 : (0 : ℚ) < (lowerGroupCard R G 0 : ℚ) :=
      Nat.cast_pos.mpr (lowerGroupCard_pos (R := R) (G := G) 0)
    refine mul_lt_mul_of_pos_right ?_ (inv_pos.mpr hg0)
    have hum : ((⌊u⌋₊ : ℚ)) ≤ u := Nat.floor_le hu.le
    have hvM : ((⌊v⌋₊ : ℚ)) ≤ v := Nat.floor_le (hu.trans huv).le
    have hu1 : u < (⌊u⌋₊ : ℚ) + 1 := Nat.lt_floor_add_one u
    have hmM : ⌊u⌋₊ ≤ ⌊v⌋₊ := Nat.floor_mono huv.le
    have hgu : (0 : ℚ) < (lowerGroupCard R G (⌊u⌋₊ + 1) : ℚ) :=
      Nat.cast_pos.mpr (lowerGroupCard_pos (R := R) (G := G) (⌊u⌋₊ + 1))
    rcases eq_or_lt_of_le hmM with heq | hlt
    ·
      rw [← heq]
      have hseg : (u - (⌊u⌋₊ : ℚ)) * (lowerGroupCard R G (⌊u⌋₊ + 1) : ℚ) <
          (v - (⌊u⌋₊ : ℚ)) * (lowerGroupCard R G (⌊u⌋₊ + 1) : ℚ) :=
        mul_lt_mul_of_pos_right (by linarith) hgu
      linarith
    ·
      have step0 : (u - (⌊u⌋₊ : ℚ)) * (lowerGroupCard R G (⌊u⌋₊ + 1) : ℚ) <
          1 * (lowerGroupCard R G (⌊u⌋₊ + 1) : ℚ) :=
        mul_lt_mul_of_pos_right (by linarith) hgu
      rw [one_mul] at step0
      have step1 : (∑ i ∈ Finset.Icc 1 (⌊u⌋₊ + 1), (lowerGroupCard R G i : ℚ)) =
          (∑ i ∈ Finset.Icc 1 ⌊u⌋₊, (lowerGroupCard R G i : ℚ)) +
            (lowerGroupCard R G (⌊u⌋₊ + 1) : ℚ) :=
        Finset.sum_Icc_succ_top (by omega : 1 ≤ ⌊u⌋₊ + 1) _
      have step2 : (∑ i ∈ Finset.Icc 1 (⌊u⌋₊ + 1), (lowerGroupCard R G i : ℚ)) ≤
          ∑ i ∈ Finset.Icc 1 ⌊v⌋₊, (lowerGroupCard R G i : ℚ) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc_right (by omega)) (fun i _ _ => Nat.cast_nonneg _)
      have step3 : (0 : ℚ) ≤ (v - ⌊v⌋₊) * lowerGroupCard R G (⌊v⌋₊ + 1) :=
        mul_nonneg (by linarith) (Nat.cast_nonneg _)
      linarith

theorem herbrandPhiRat_monotone [Finite G] : Monotone (herbrandPhiRat R G) :=
  (herbrandPhiRat_strictMono (R := R) (G := G)).monotone

theorem herbrandPhiRat_injective [Finite G] : Function.Injective (herbrandPhiRat R G) :=
  (herbrandPhiRat_strictMono (R := R) (G := G)).injective

theorem exists_natCast_le_herbrandPhiRat [Finite G] (v : ℚ) :
    ∃ n : ℕ, v ≤ herbrandPhiRat R G n := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, v * (lowerGroupCard R G 0 : ℚ) ≤ n :=
    ⟨⌈v * (lowerGroupCard R G 0 : ℚ)⌉₊, Nat.le_ceil _⟩
  refine ⟨n, ?_⟩
  have hg0 : (0 : ℚ) < (lowerGroupCard R G 0 : ℚ) :=
    Nat.cast_pos.mpr (lowerGroupCard_pos (R := R) (G := G) 0)
  have h2 : (n : ℚ) ≤ ∑ i ∈ Finset.Icc 1 n, (lowerGroupCard R G i : ℚ) := by
    have hcard : (Finset.Icc 1 n).card = n := by rw [Nat.card_Icc]; omega
    calc (n : ℚ) = (Finset.Icc 1 n).card • (1 : ℚ) := by rw [hcard, nsmul_eq_mul, mul_one]
      _ ≤ ∑ i ∈ Finset.Icc 1 n, (lowerGroupCard R G i : ℚ) :=
          Finset.card_nsmul_le_sum _ _ _ (fun i _ => one_le_lowerGroupCard_cast i)
  have h3 : v * (lowerGroupCard R G 0 : ℚ) ≤
      ∑ i ∈ Finset.Icc 1 n, (lowerGroupCard R G i : ℚ) := hn.trans h2
  rw [herbrandPhiRat_natCast]
  calc v = v * (lowerGroupCard R G 0 : ℚ) / (lowerGroupCard R G 0 : ℚ) := by
        rw [mul_div_assoc, div_self hg0.ne', mul_one]
    _ ≤ (∑ i ∈ Finset.Icc 1 n, (lowerGroupCard R G i : ℚ)) /
          (lowerGroupCard R G 0 : ℚ) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right h3 (inv_nonneg.mpr hg0.le)

variable (R G) in

noncomputable def herbrandPsiRat : ℚ → ℚ :=
  Function.invFun (herbrandPhiRat R G)

theorem herbrandPsiRat_herbrandPhiRat [Finite G] (u : ℚ) :
    herbrandPsiRat R G (herbrandPhiRat R G u) = u :=
  Function.leftInverse_invFun (herbrandPhiRat_injective (R := R) (G := G)) u

theorem herbrandPsiRat_zero [Finite G] : herbrandPsiRat R G 0 = 0 := by
  have h := herbrandPsiRat_herbrandPhiRat (R := R) (G := G) 0
  rwa [herbrandPhiRat_zero] at h

variable (R G) in

noncomputable def upperGroupRatIndex (v : ℚ) : ℕ :=
  sInf {n : ℕ | v ≤ herbrandPhiRat R G n}

variable (R G) in

noncomputable def upperGroupRat (v : ℚ) : Subgroup G :=
  lowerGroup R G (upperGroupRatIndex R G v)

theorem upperGroupRatIndex_of_nonpos {v : ℚ} (h : v ≤ 0) :
    upperGroupRatIndex R G v = 0 :=
  Nat.sInf_eq_zero.mpr (Or.inl (by simpa using h))

@[simp] theorem upperGroupRatIndex_zero : upperGroupRatIndex R G 0 = 0 :=
  upperGroupRatIndex_of_nonpos le_rfl

@[simp] theorem mem_upperGroupRat {σ : G} {v : ℚ} :
    σ ∈ upperGroupRat R G v ↔
      ∀ x : R, σ • x - x ∈ (maximalIdeal R) ^ (upperGroupRatIndex R G v + 1) :=
  Iff.rfl

theorem upperGroupRat_of_nonpos {v : ℚ} (h : v ≤ 0) :
    upperGroupRat R G v = lowerGroup R G 0 :=
  congrArg (lowerGroup R G) (upperGroupRatIndex_of_nonpos h)

@[simp] theorem upperGroupRat_zero :
    upperGroupRat R G 0 = lowerGroup R G 0 :=
  upperGroupRat_of_nonpos le_rfl

theorem upperGroupRat_zero_eq_ker :
    upperGroupRat R G 0 =
      MonoidHom.ker (MulSemiringAction.toRingAut G (ResidueField R)) :=
  upperGroupRat_zero.trans lowerGroup_zero_eq_ker

theorem upperGroupRat_le_zero (v : ℚ) :
    upperGroupRat R G v ≤ lowerGroup R G 0 :=
  lowerGroup_le_zero _

theorem le_herbrandPhiRat_upperGroupRatIndex [Finite G] (v : ℚ) :
    v ≤ herbrandPhiRat R G (upperGroupRatIndex R G v : ℕ) := by
  have hne : {n : ℕ | v ≤ herbrandPhiRat R G n}.Nonempty := exists_natCast_le_herbrandPhiRat v
  have hmem : sInf {n : ℕ | v ≤ herbrandPhiRat R G n} ∈ {n : ℕ | v ≤ herbrandPhiRat R G n} :=
    Nat.sInf_mem hne
  exact hmem

theorem upperGroupRatIndex_le {v : ℚ} {n : ℕ} (h : v ≤ herbrandPhiRat R G n) :
    upperGroupRatIndex R G v ≤ n := by
  have hmem : n ∈ {m : ℕ | v ≤ herbrandPhiRat R G m} := h
  exact Nat.sInf_le hmem

theorem upperGroupRatIndex_monotone [Finite G] :
    Monotone (upperGroupRatIndex R G) := by
  intro v w hvw
  exact upperGroupRatIndex_le (hvw.trans (le_herbrandPhiRat_upperGroupRatIndex w))

theorem upperGroupRat_antitone [Finite G] :
    Antitone (upperGroupRat R G) := by
  intro v w hvw
  exact (lowerGroup_antitone _ _) (upperGroupRatIndex_monotone (R := R) (G := G) hvw)

theorem upperGroupRatIndex_herbrandPhiRat_natCast [Finite G] (n : ℕ) :
    upperGroupRatIndex R G (herbrandPhiRat R G n) = n := by
  apply le_antisymm
  · exact upperGroupRatIndex_le le_rfl
  · have h1 : herbrandPhiRat R G n ≤
        herbrandPhiRat R G (upperGroupRatIndex R G (herbrandPhiRat R G n) : ℕ) :=
      le_herbrandPhiRat_upperGroupRatIndex _
    exact Nat.cast_le.mp ((herbrandPhiRat_strictMono (R := R) (G := G)).le_iff_le.mp h1)

theorem upperGroupRat_herbrandPhiRat_natCast [Finite G] (n : ℕ) :
    upperGroupRat R G (herbrandPhiRat R G n) = lowerGroup R G n :=
  congrArg (lowerGroup R G) (upperGroupRatIndex_herbrandPhiRat_natCast n)

variable (R G) in

def UpperGroupRatQuotientCompat (S : Type*) [CommRing S] [IsLocalRing S]
    (H : Subgroup G) [H.Normal] [MulSemiringAction (G ⧸ H) S] : Prop :=
  ∀ v : ℚ, 0 ≤ v →
    (upperGroupRat R G v).map (QuotientGroup.mk' H) =
      upperGroupRat S (G ⧸ H) v

end

end

section

section
open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

theorem herbrandPhiRat_natCast_succ (m : ℕ) :
    herbrandPhiRat R G ((m : ℚ) + 1) =
      herbrandPhiRat R G m +
        (lowerGroupCard R G (m + 1) : ℚ) / (lowerGroupCard R G 0 : ℚ) := by
  have hcast : ((m : ℚ) + 1) = ((m + 1 : ℕ) : ℚ) := by push_cast; ring
  have hsum : (∑ i ∈ Finset.Icc 1 (m + 1), (lowerGroupCard R G i : ℚ)) =
      (∑ i ∈ Finset.Icc 1 m, (lowerGroupCard R G i : ℚ)) +
        (lowerGroupCard R G (m + 1) : ℚ) :=
    Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1) _
  rw [hcast, herbrandPhiRat_natCast, herbrandPhiRat_natCast, hsum, add_div]

theorem herbrandPhiRat_segment (m : ℕ) {u : ℚ} (h1 : (m : ℚ) ≤ u) (h2 : u ≤ (m : ℚ) + 1) :
    herbrandPhiRat R G u = herbrandPhiRat R G m +
      (u - m) * (lowerGroupCard R G (m + 1) : ℚ) / (lowerGroupCard R G 0 : ℚ) := by
  rcases eq_or_lt_of_le h2 with heq | hlt
  ·
    rw [heq, herbrandPhiRat_natCast_succ]
    ring
  · rcases le_or_gt u 0 with hu | hu
    ·
      have hm0 : m = 0 := by
        by_contra hm
        have hm1 : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
        linarith
      subst hm0
      have hu0 : u = 0 := le_antisymm hu (by simpa using h1)
      subst hu0
      simp
    ·
      have hfloor : ⌊u⌋₊ = m := by
        rw [Nat.floor_eq_iff hu.le]
        exact ⟨h1, hlt⟩
      rw [herbrandPhiRat_of_pos hu, hfloor, herbrandPhiRat_natCast, add_div]

theorem herbrandPhiRat_segment_solve [Finite G] (m : ℕ) {v : ℚ}
    (h1 : herbrandPhiRat R G m ≤ v) (h2 : v ≤ herbrandPhiRat R G ((m : ℚ) + 1)) :
    herbrandPhiRat R G ((m : ℚ) + (v - herbrandPhiRat R G m) *
      (lowerGroupCard R G 0 : ℚ) / (lowerGroupCard R G (m + 1) : ℚ)) = v := by
  have hg0 : (0 : ℚ) < (lowerGroupCard R G 0 : ℚ) :=
    Nat.cast_pos.mpr (lowerGroupCard_pos (R := R) (G := G) 0)
  have hgm : (0 : ℚ) < (lowerGroupCard R G (m + 1) : ℚ) :=
    Nat.cast_pos.mpr (lowerGroupCard_pos (R := R) (G := G) (m + 1))
  have hg0' : (lowerGroupCard R G 0 : ℚ) ≠ 0 := hg0.ne'
  have hgm' : (lowerGroupCard R G (m + 1) : ℚ) ≠ 0 := hgm.ne'

  have hrec : herbrandPhiRat R G ((m : ℚ) + 1) =
      herbrandPhiRat R G m +
        (lowerGroupCard R G (m + 1) : ℚ) / (lowerGroupCard R G 0 : ℚ) :=
    herbrandPhiRat_natCast_succ m
  have hsub : (v - herbrandPhiRat R G m) * (lowerGroupCard R G 0 : ℚ) ≤
      (lowerGroupCard R G (m + 1) : ℚ) := by
    have h2' : v - herbrandPhiRat R G m ≤
        (lowerGroupCard R G (m + 1) : ℚ) / (lowerGroupCard R G 0 : ℚ) := by
      rw [hrec] at h2
      linarith
    calc (v - herbrandPhiRat R G m) * (lowerGroupCard R G 0 : ℚ)
        ≤ ((lowerGroupCard R G (m + 1) : ℚ) / (lowerGroupCard R G 0 : ℚ)) *
            (lowerGroupCard R G 0 : ℚ) := mul_le_mul_of_nonneg_right h2' hg0.le
      _ = (lowerGroupCard R G (m + 1) : ℚ) := by
          rw [div_mul_eq_mul_div, mul_div_assoc, div_self hg0', mul_one]
  have ht0 : 0 ≤ (v - herbrandPhiRat R G m) *
      (lowerGroupCard R G 0 : ℚ) / (lowerGroupCard R G (m + 1) : ℚ) :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr h1) hg0.le) hgm.le
  have ht1 : (v - herbrandPhiRat R G m) *
      (lowerGroupCard R G 0 : ℚ) / (lowerGroupCard R G (m + 1) : ℚ) ≤ 1 := by
    rw [div_le_one hgm]
    exact hsub

  have hA : (m : ℚ) ≤ (m : ℚ) + (v - herbrandPhiRat R G m) *
      (lowerGroupCard R G 0 : ℚ) / (lowerGroupCard R G (m + 1) : ℚ) := by
    linarith
  have hB : (m : ℚ) + (v - herbrandPhiRat R G m) *
      (lowerGroupCard R G 0 : ℚ) / (lowerGroupCard R G (m + 1) : ℚ) ≤
      (m : ℚ) + 1 := by
    linarith
  rw [herbrandPhiRat_segment m hA hB]
  field_simp
  ring

theorem herbrandPhiRat_surjective [Finite G] : Function.Surjective (herbrandPhiRat R G) := by
  intro v
  rcases le_or_gt v 0 with hv | hv
  · exact ⟨v, herbrandPhiRat_of_nonpos hv⟩
  · have hvn : v ≤ herbrandPhiRat R G (upperGroupRatIndex R G v : ℕ) :=
      le_herbrandPhiRat_upperGroupRatIndex v
    have hn0 : upperGroupRatIndex R G v ≠ 0 := by
      intro h0
      rw [h0, Nat.cast_zero, herbrandPhiRat_zero] at hvn
      exact absurd hvn (not_le.mpr hv)
    obtain ⟨m, hm⟩ : ∃ m, upperGroupRatIndex R G v = m + 1 :=
      ⟨upperGroupRatIndex R G v - 1, by omega⟩
    have hmlt : herbrandPhiRat R G m < v := by
      by_contra hle
      rw [not_lt] at hle
      have hcontra := upperGroupRatIndex_le hle
      omega
    have hvle : v ≤ herbrandPhiRat R G ((m : ℚ) + 1) := by
      rw [hm] at hvn
      push_cast at hvn
      exact hvn
    exact ⟨_, herbrandPhiRat_segment_solve m hmlt.le hvle⟩

theorem herbrandPhiRat_bijective [Finite G] : Function.Bijective (herbrandPhiRat R G) :=
  ⟨herbrandPhiRat_injective, herbrandPhiRat_surjective⟩

theorem herbrandPhiRat_herbrandPsiRat [Finite G] (v : ℚ) :
    herbrandPhiRat R G (herbrandPsiRat R G v) = v :=
  Function.rightInverse_invFun (herbrandPhiRat_surjective (R := R) (G := G)) v

theorem herbrandPsiRat_rightInverse [Finite G] :
    Function.RightInverse (herbrandPsiRat R G) (herbrandPhiRat R G) :=
  herbrandPhiRat_herbrandPsiRat (R := R) (G := G)

theorem herbrandPsiRat_leftInverse [Finite G] :
    Function.LeftInverse (herbrandPsiRat R G) (herbrandPhiRat R G) :=
  herbrandPsiRat_herbrandPhiRat (R := R) (G := G)

theorem herbrandPsiRat_strictMono [Finite G] : StrictMono (herbrandPsiRat R G) := by
  intro v w hvw
  have h1 : herbrandPhiRat R G (herbrandPsiRat R G v) < herbrandPhiRat R G (herbrandPsiRat R G w) := by
    rwa [herbrandPhiRat_herbrandPsiRat, herbrandPhiRat_herbrandPsiRat]
  exact (herbrandPhiRat_strictMono (R := R) (G := G)).lt_iff_lt.mp h1

theorem herbrandPsiRat_monotone [Finite G] : Monotone (herbrandPsiRat R G) :=
  (herbrandPsiRat_strictMono (R := R) (G := G)).monotone

theorem herbrandPsiRat_injective [Finite G] : Function.Injective (herbrandPsiRat R G) :=
  (herbrandPsiRat_strictMono (R := R) (G := G)).injective

theorem herbrandPsiRat_surjective [Finite G] : Function.Surjective (herbrandPsiRat R G) :=
  fun u => ⟨herbrandPhiRat R G u, herbrandPsiRat_herbrandPhiRat u⟩

theorem herbrandPsiRat_bijective [Finite G] : Function.Bijective (herbrandPsiRat R G) :=
  ⟨herbrandPsiRat_injective, herbrandPsiRat_surjective⟩

theorem herbrandPsiRat_le_iff [Finite G] {v u : ℚ} :
    herbrandPsiRat R G v ≤ u ↔ v ≤ herbrandPhiRat R G u := by
  constructor
  · intro h
    have h2 := herbrandPhiRat_monotone (R := R) (G := G) h
    rwa [herbrandPhiRat_herbrandPsiRat] at h2
  · intro h
    have h2 := herbrandPsiRat_monotone (R := R) (G := G) h
    rwa [herbrandPsiRat_herbrandPhiRat] at h2

theorem le_herbrandPsiRat_iff [Finite G] {v u : ℚ} :
    u ≤ herbrandPsiRat R G v ↔ herbrandPhiRat R G u ≤ v := by
  constructor
  · intro h
    have h2 := herbrandPhiRat_monotone (R := R) (G := G) h
    rwa [herbrandPhiRat_herbrandPsiRat] at h2
  · intro h
    have h2 := herbrandPsiRat_monotone (R := R) (G := G) h
    rwa [herbrandPsiRat_herbrandPhiRat] at h2

theorem herbrandPsiRat_lt_iff [Finite G] {v u : ℚ} :
    herbrandPsiRat R G v < u ↔ v < herbrandPhiRat R G u := by
  rw [← not_le, ← not_le, le_herbrandPsiRat_iff]

theorem lt_herbrandPsiRat_iff [Finite G] {v u : ℚ} :
    u < herbrandPsiRat R G v ↔ herbrandPhiRat R G u < v := by
  rw [← not_le, ← not_le, herbrandPsiRat_le_iff]

theorem herbrandPsiRat_of_nonpos [Finite G] {v : ℚ} (h : v ≤ 0) : herbrandPsiRat R G v = v := by
  have h1 := herbrandPsiRat_herbrandPhiRat (R := R) (G := G) v
  rwa [herbrandPhiRat_of_nonpos h] at h1

theorem herbrandPsiRat_nonneg [Finite G] {v : ℚ} (h : 0 ≤ v) : 0 ≤ herbrandPsiRat R G v := by
  have h1 := herbrandPsiRat_monotone (R := R) (G := G) h
  rwa [herbrandPsiRat_zero] at h1

theorem herbrandPsiRat_pos [Finite G] {v : ℚ} (h : 0 < v) : 0 < herbrandPsiRat R G v := by
  have h1 := herbrandPsiRat_strictMono (R := R) (G := G) h
  rwa [herbrandPsiRat_zero] at h1

theorem herbrandPsiRat_segment [Finite G] (m : ℕ) {v : ℚ}
    (h1 : herbrandPhiRat R G m ≤ v) (h2 : v ≤ herbrandPhiRat R G ((m : ℚ) + 1)) :
    herbrandPsiRat R G v = (m : ℚ) + (v - herbrandPhiRat R G m) *
      (lowerGroupCard R G 0 : ℚ) / (lowerGroupCard R G (m + 1) : ℚ) := by
  have hsolve := herbrandPhiRat_segment_solve (R := R) (G := G) m h1 h2
  have h3 := herbrandPsiRat_herbrandPhiRat (R := R) (G := G) ((m : ℚ) + (v - herbrandPhiRat R G m) *
      (lowerGroupCard R G 0 : ℚ) / (lowerGroupCard R G (m + 1) : ℚ))
  rw [hsolve] at h3
  exact h3

theorem upperGroupRatIndex_eq_zero_iff [Finite G] {v : ℚ} :
    upperGroupRatIndex R G v = 0 ↔ v ≤ 0 := by
  constructor
  · intro h
    by_contra hv
    rw [not_le] at hv
    have hvn := le_herbrandPhiRat_upperGroupRatIndex (R := R) (G := G) v
    rw [h, Nat.cast_zero, herbrandPhiRat_zero] at hvn
    exact absurd hvn (not_le.mpr hv)
  · exact upperGroupRatIndex_of_nonpos

theorem upperGroupRatIndex_eq_succ_iff [Finite G] {v : ℚ} {m : ℕ} :
    upperGroupRatIndex R G v = m + 1 ↔
      herbrandPhiRat R G m < v ∧ v ≤ herbrandPhiRat R G ((m : ℚ) + 1) := by
  constructor
  · intro h
    constructor
    · by_contra hle
      rw [not_lt] at hle
      have hcontra := upperGroupRatIndex_le hle
      omega
    · have hvn := le_herbrandPhiRat_upperGroupRatIndex (R := R) (G := G) v
      rw [h] at hvn
      push_cast at hvn
      exact hvn
  · rintro ⟨h1, h2⟩
    have hub : upperGroupRatIndex R G v ≤ m + 1 := by
      apply upperGroupRatIndex_le
      push_cast
      exact h2
    have hlb : m < upperGroupRatIndex R G v := by
      by_contra hle
      rw [not_lt] at hle
      have h3 : herbrandPhiRat R G ((upperGroupRatIndex R G v : ℕ) : ℚ) ≤
          herbrandPhiRat R G (m : ℚ) :=
        herbrandPhiRat_monotone (R := R) (G := G) (by exact_mod_cast hle)
      have h4 := le_herbrandPhiRat_upperGroupRatIndex (R := R) (G := G) v
      linarith
    omega

theorem upperGroupRatIndex_eq_iff [Finite G] {v : ℚ} {n : ℕ} :
    upperGroupRatIndex R G v = n ↔
      (n = 0 ∧ v ≤ herbrandPhiRat R G 0) ∨
        (herbrandPhiRat R G ((n - 1 : ℕ) : ℚ) < v ∧ v ≤ herbrandPhiRat R G ((n : ℕ) : ℚ)) := by
  rcases n with _ | m
  · rw [upperGroupRatIndex_eq_zero_iff]
    constructor
    · intro h
      exact Or.inl ⟨rfl, by simpa using h⟩
    · rintro (⟨_, h⟩ | ⟨h1, h2⟩)
      · simpa using h
      ·
        simp only [Nat.zero_sub, Nat.cast_zero] at h1 h2
        linarith
  · rw [upperGroupRatIndex_eq_succ_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine Or.inr ⟨?_, ?_⟩
      · simpa using h1
      · push_cast
        exact h2
    · rintro (⟨h0, _⟩ | ⟨h1, h2⟩)
      · exact absurd h0 (by omega)
      · constructor
        · simpa using h1
        · push_cast at h2
          exact h2

theorem upperGroupRat_of_lt_of_le [Finite G] {v : ℚ} {m : ℕ}
    (h1 : herbrandPhiRat R G m < v) (h2 : v ≤ herbrandPhiRat R G ((m : ℚ) + 1)) :
    upperGroupRat R G v = lowerGroup R G (m + 1) :=
  congrArg (lowerGroup R G)
    ((upperGroupRatIndex_eq_succ_iff (R := R) (G := G)).mpr ⟨h1, h2⟩)

theorem upperGroupRat_eq_of_segment [Finite G] {v w : ℚ} {m : ℕ}
    (hv1 : herbrandPhiRat R G m < v) (hv2 : v ≤ herbrandPhiRat R G ((m : ℚ) + 1))
    (hw1 : herbrandPhiRat R G m < w) (hw2 : w ≤ herbrandPhiRat R G ((m : ℚ) + 1)) :
    upperGroupRat R G v = upperGroupRat R G w := by
  rw [upperGroupRat_of_lt_of_le hv1 hv2, upperGroupRat_of_lt_of_le hw1 hw2]

theorem upperGroupRatIndex_eq_ceil_herbrandPsiRat [Finite G] (v : ℚ) :
    upperGroupRatIndex R G v = ⌈herbrandPsiRat R G v⌉₊ := by
  rcases le_or_gt v 0 with hv | hv
  · rw [upperGroupRatIndex_of_nonpos hv, herbrandPsiRat_of_nonpos hv]
    exact (Nat.ceil_eq_zero.mpr hv).symm
  · obtain ⟨m, hm⟩ : ∃ m, upperGroupRatIndex R G v = m + 1 := by
      have h0 : upperGroupRatIndex R G v ≠ 0 := by
        rw [Ne, upperGroupRatIndex_eq_zero_iff]
        exact not_le.mpr hv
      exact ⟨upperGroupRatIndex R G v - 1, by omega⟩
    obtain ⟨h1, h2⟩ := (upperGroupRatIndex_eq_succ_iff (R := R) (G := G)).mp hm
    have hpsi1 : (m : ℚ) < herbrandPsiRat R G v :=
      (lt_herbrandPsiRat_iff (R := R) (G := G)).mpr h1
    have hpsi2 : herbrandPsiRat R G v ≤ (m : ℚ) + 1 :=
      (herbrandPsiRat_le_iff (R := R) (G := G)).mpr h2
    rw [hm]
    refine ((Nat.ceil_eq_iff (by omega : m + 1 ≠ 0)).mpr ?_).symm
    constructor
    · simpa using hpsi1
    · push_cast
      exact hpsi2

theorem upperGroupRat_eq_ceil_herbrandPsiRat [Finite G] (v : ℚ) :
    upperGroupRat R G v = lowerGroup R G ⌈herbrandPsiRat R G v⌉₊ :=
  congrArg (lowerGroup R G) (upperGroupRatIndex_eq_ceil_herbrandPsiRat v)

end

end

end Langlands.Ramification
