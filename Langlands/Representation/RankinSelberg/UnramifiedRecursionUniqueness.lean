import Langlands.Representation.Unramified.MinusculeCosets

/-!
# Uniqueness for the minuscule Hecke recursion on partitions

Let `d` be a complex function on integer exponent vectors `Fin m → ℤ` that vanishes
on non-antitone vectors. Suppose that for every partition exponent `lam` (antitone and
nonnegative) and every `1 ≤ k ≤ m`,

`c k * d lam = ∑_(|S| = k) w S * d (lam + 1_S)`,

where `1_S` is the indicator exponent of `S`, and the weight of the initial segment
`{0, …, k - 1}` is nonzero. If `d 0 = 0`, then `d` vanishes on all partition exponents.
The proof is a strong induction on the weighted size `∑ i, (m - i) * lam i`.
-/

noncomputable section

namespace Langlands.RankinSelberg.UnramifiedWhittaker

open Langlands.Unramified.MinusculeCosets

/-! ### Sums of distinct natural numbers -/

/-- The sum of a finite set of natural numbers is at least `0 + 1 + ⋯ + (card - 1)`, with
equality only for the initial segment. -/
theorem sum_range_card_le_and_eq (T : Finset ℕ) :
    ∑ i ∈ Finset.range T.card, i ≤ ∑ i ∈ T, i ∧
      (∑ i ∈ T, i = ∑ i ∈ Finset.range T.card, i → T = Finset.range T.card) := by
  induction T using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hcard : s.card ≤ a := by
      have hsub : s ⊆ Finset.range a := fun x hx => Finset.mem_range.2 (ha x hx)
      simpa using Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem has, Finset.sum_insert has, Finset.sum_range_succ]
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨by omega, fun h => ?_⟩
    have hs : ∑ i ∈ s, i = ∑ i ∈ Finset.range s.card, i := by omega
    have hac : a = s.card := by omega
    rw [Finset.range_add_one, ← ih2 hs, hac]

theorem sum_range_card_le (T : Finset ℕ) :
    ∑ i ∈ Finset.range T.card, i ≤ ∑ i ∈ T, i :=
  (sum_range_card_le_and_eq T).1

theorem sum_range_card_lt (T : Finset ℕ) (hT : T ≠ Finset.range T.card) :
    ∑ i ∈ Finset.range T.card, i < ∑ i ∈ T, i :=
  lt_of_le_of_ne (sum_range_card_le T) fun h => hT ((sum_range_card_le_and_eq T).2 h.symm)

/-! ### Initial segments of `Fin m` -/

variable {m : ℕ}

/-- The first `k` coordinates. -/
def initialSegment (m k : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun j => j.val < k

theorem mem_initialSegment {k : ℕ} (j : Fin m) : j ∈ initialSegment m k ↔ j.val < k := by
  simp [initialSegment]

theorem map_initialSegment {k : ℕ} (hk : k ≤ m) :
    (initialSegment m k).map Fin.valEmbedding = Finset.range k := by
  ext x
  simp only [Finset.mem_map, mem_initialSegment, Fin.valEmbedding_apply, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact hj
  · intro hx
    exact ⟨⟨x, by omega⟩, hx, rfl⟩

theorem card_initialSegment {k : ℕ} (hk : k ≤ m) : (initialSegment m k).card = k := by
  rw [← Finset.card_map Fin.valEmbedding, map_initialSegment hk, Finset.card_range]

/-- A set of indices of size `k` other than the initial segment has a strictly larger sum
of indices. -/
theorem sum_initialSegment_lt {k : ℕ} {S : Finset (Fin m)} (hS : S.card = k)
    (hne : S ≠ initialSegment m k) :
    ∑ i ∈ initialSegment m k, (i : ℕ) < ∑ i ∈ S, (i : ℕ) := by
  have hk : k ≤ m := by
    have := Finset.card_le_univ S
    simpa [hS] using this
  set T := S.map Fin.valEmbedding with hT
  have hTcard : T.card = k := by rw [hT, Finset.card_map, hS]
  have hTne : T ≠ Finset.range T.card := by
    rw [hTcard, ← map_initialSegment hk]
    exact fun h => hne (Finset.map_injective Fin.valEmbedding h)
  have h := sum_range_card_lt T hTne
  rw [hTcard, ← map_initialSegment hk, Finset.sum_map, hT, Finset.sum_map] at h
  simpa using h

/-- A downward closed set of indices is the initial segment of its cardinality. -/
theorem eq_initialSegment_of_downward {D : Finset (Fin m)}
    (hD : ∀ i j, i ≤ j → j ∈ D → i ∈ D) : D = initialSegment m D.card := by
  ext j
  rw [mem_initialSegment]
  constructor
  · intro hj
    have hsub : Finset.Iic j ⊆ D := fun i hi => hD i j (Finset.mem_Iic.1 hi) hj
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro hj
    by_contra hjD
    have hsub : D ⊆ Finset.Iio j := fun i hi => by
      rw [Finset.mem_Iio]
      by_contra hij
      exact hjD (hD j i (not_lt.1 hij) hi)
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

/-! ### Partition exponents and the weighted size -/

/-- An antitone, nonnegative exponent vector. -/
def IsPartitionExponent (lam : Fin m → ℤ) : Prop :=
  Antitone lam ∧ ∀ i, 0 ≤ lam i

/-- The weighted size `∑ i, (m - i) * lam i`. -/
def weightedSize (lam : Fin m → ℤ) : ℤ :=
  ∑ i : Fin m, ((m : ℤ) - (i : ℕ)) * lam i

theorem weightedSize_add (lam mu : Fin m → ℤ) :
    weightedSize (lam + mu) = weightedSize lam + weightedSize mu := by
  simp only [weightedSize, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem weightedSize_subsetExponent (S : Finset (Fin m)) :
    weightedSize (subsetExponent S) = (S.card : ℤ) * m - ∑ i ∈ S, ((i : ℕ) : ℤ) := by
  simp only [weightedSize, subsetExponent, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_sub_distrib]
  simp [mul_comm]

theorem weightedSize_nonneg {lam : Fin m → ℤ} (h : ∀ i, 0 ≤ lam i) : 0 ≤ weightedSize lam := by
  apply Finset.sum_nonneg
  intro i _
  have : ((i : ℕ) : ℤ) < m := by exact_mod_cast i.isLt
  exact mul_nonneg (by omega) (h i)

theorem weightedSize_pos {lam : Fin m → ℤ} (h : ∀ i, 0 ≤ lam i) (hne : lam ≠ 0) :
    0 < weightedSize lam := by
  obtain ⟨j, hj⟩ : ∃ j, lam j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  have hjpos : 0 < lam j := lt_of_le_of_ne (h j) (Ne.symm hj)
  have hmj : ((j : ℕ) : ℤ) < m := by exact_mod_cast j.isLt
  calc 0 < ((m : ℤ) - (j : ℕ)) * lam j := mul_pos (by omega) hjpos
    _ ≤ weightedSize lam := by
      apply Finset.single_le_sum (f := fun i : Fin m => ((m : ℤ) - (i : ℕ)) * lam i)
        (fun i _ => ?_) (Finset.mem_univ j)
      have : ((i : ℕ) : ℤ) < m := by exact_mod_cast i.isLt
      exact mul_nonneg (by omega) (h i)

/-! ### The recursion -/

/-- The minuscule Hecke recursion on partition exponents, with weights `w`: at every
partition exponent `lam` and every `1 ≤ k ≤ m`, some scalar `c` satisfies
`c * d lam = ∑_(|S| = k) w S * d (lam + 1_S)`. The scalar may depend on `lam` and `k`. -/
def SatisfiesHeckeRecursion (w : Finset (Fin m) → ℂ) (d : (Fin m → ℤ) → ℂ) : Prop :=
  ∀ lam : Fin m → ℤ, IsPartitionExponent lam → ∀ k : ℕ, 1 ≤ k → k ≤ m →
    ∃ c : ℂ, c * d lam =
      ∑ S : {S : Finset (Fin m) // S.card = k}, w S.1 * d (lam + subsetExponent S.1)

/-- A solution of the recursion that vanishes off antitone vectors and at zero vanishes on
every partition exponent, if the weights of initial segments are nonzero. -/
theorem eq_zero_of_satisfiesHeckeRecursion {w : Finset (Fin m) → ℂ}
    {d : (Fin m → ℤ) → ℂ} (hw : ∀ k, k ≤ m → w (initialSegment m k) ≠ 0)
    (hd : SatisfiesHeckeRecursion w d) (hanti : ∀ lam, ¬ Antitone lam → d lam = 0)
    (h0 : d 0 = 0) : ∀ lam, IsPartitionExponent lam → d lam = 0 := by
  classical
  suffices H : ∀ N : ℕ, ∀ lam : Fin m → ℤ, IsPartitionExponent lam →
      (weightedSize lam).toNat = N → d lam = 0 from
    fun lam hlam => H _ lam hlam rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro mu hmu hN
  by_cases hz : mu = 0
  · rw [hz, h0]
  -- the positive coordinates form an initial segment
  set D : Finset (Fin m) := Finset.univ.filter fun i => 0 < mu i with hDdef
  set k := D.card with hkdef
  have hDdown : ∀ i j, i ≤ j → j ∈ D → i ∈ D := by
    intro i j hij hj
    simp only [hDdef, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact lt_of_lt_of_le hj (hmu.1 hij)
  have hDinit : D = initialSegment m k := eq_initialSegment_of_downward hDdown
  have hkm : k ≤ m := by
    have := Finset.card_le_univ D
    simpa [hkdef] using this
  have hk1 : 1 ≤ k := by
    obtain ⟨j, hj⟩ : ∃ j, mu j ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hz (funext hall)
    have hjD : j ∈ D := by
      simp only [hDdef, Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_le_of_ne (hmu.2 j) (Ne.symm hj)
    exact Finset.card_pos.2 ⟨j, hjD⟩
  -- the lowered exponent
  set lam : Fin m → ℤ := mu - subsetExponent D with hlamdef
  have hmuD : ∀ i, i ∈ D ↔ 0 < mu i := fun i => by simp [hDdef]
  have hlam_apply : ∀ i, lam i = if i ∈ D then mu i - 1 else mu i := by
    intro i
    simp only [hlamdef, Pi.sub_apply, subsetExponent]
    split_ifs <;> ring
  have hlamP : IsPartitionExponent lam := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hlam_apply, hlam_apply]
      have hmij := hmu.1 hij
      by_cases hj : j ∈ D
      · have hi : i ∈ D := hDdown i j hij hj
        simp only [hi, hj, ite_true]
        omega
      · by_cases hi : i ∈ D
        · simp only [hi, hj, ite_true, ite_false]
          rw [hmuD] at hi hj
          omega
        · simp only [hi, hj, ite_false]
          exact hmij
    · rw [hlam_apply]
      split_ifs with hi
      · rw [hmuD] at hi
        omega
      · exact hmu.2 i
  have hmu_eq : lam + subsetExponent D = mu := by
    rw [hlamdef, sub_add_cancel]
  have hWmu : weightedSize mu = weightedSize lam + weightedSize (subsetExponent D) := by
    rw [← weightedSize_add, hmu_eq]
  have hWD_pos : 0 < weightedSize (subsetExponent D) := by
    apply weightedSize_pos
    · intro i
      simp only [subsetExponent]
      split_ifs <;> norm_num
    · intro h
      obtain ⟨j, hj⟩ := Finset.card_pos.1 (lt_of_lt_of_le zero_lt_one hk1)
      have := congrFun h j
      simp [subsetExponent, hj] at this
  have hWlam := weightedSize_nonneg hlamP.2
  have hWmu_nat : weightedSize mu = (N : ℤ) := by
    rw [← hN, Int.toNat_of_nonneg (weightedSize_nonneg hmu.2)]
  -- vanishing of all smaller terms
  have hsmall : ∀ nu : Fin m → ℤ, (∀ i, 0 ≤ nu i) →
      weightedSize nu < weightedSize mu → d nu = 0 := by
    intro nu hnu hlt
    by_cases hanti_nu : Antitone nu
    · refine ih (weightedSize nu).toNat ?_ nu ⟨hanti_nu, hnu⟩ rfl
      have := weightedSize_nonneg hnu
      omega
    · exact hanti nu hanti_nu
  have hdlam : d lam = 0 := hsmall lam hlamP.2 (by omega)
  -- the recursion at `lam`
  obtain ⟨c, hrec⟩ := hd lam hlamP k hk1 hkm
  rw [hdlam, mul_zero] at hrec
  have hDk : D.card = k := rfl
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨D, hDk⟩ : {S : Finset (Fin m) // S.card = k}))]
    at hrec
  have hrest : ∑ S ∈ Finset.univ.erase (⟨D, hDk⟩ : {S : Finset (Fin m) // S.card = k}),
      w S.1 * d (lam + subsetExponent S.1) = 0 := by
    apply Finset.sum_eq_zero
    intro S hS
    have hSne : S.1 ≠ D := by
      intro h
      apply (Finset.mem_erase.1 hS).1
      exact Subtype.ext h
    have hnonneg : ∀ i, 0 ≤ (lam + subsetExponent S.1) i := by
      intro i
      simp only [Pi.add_apply, subsetExponent]
      have := hlamP.2 i
      split_ifs <;> omega
    have hlt : weightedSize (lam + subsetExponent S.1) < weightedSize mu := by
      rw [hWmu, weightedSize_add, weightedSize_subsetExponent, weightedSize_subsetExponent,
        S.2, hDk]
      have hne' : S.1 ≠ initialSegment m k := by rw [← hDinit]; exact hSne
      have hsum := sum_initialSegment_lt S.2 hne'
      have hsum' : ∑ i ∈ D, ((i : ℕ) : ℤ) < ∑ i ∈ S.1, ((i : ℕ) : ℤ) := by
        rw [hDinit]
        exact_mod_cast hsum
      linarith
    rw [hsmall _ hnonneg hlt, mul_zero]
  rw [hrest, add_zero, hmu_eq] at hrec
  have hwD : w D ≠ 0 := by rw [hDinit]; exact hw k hkm
  exact (mul_eq_zero.1 hrec.symm).resolve_left hwD

end Langlands.RankinSelberg.UnramifiedWhittaker
