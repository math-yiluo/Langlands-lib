import Langlands.Cohomology.Weights.Algebraic
import Langlands.Cohomology.Weights.Separation

/-!
# Proof of algebraic weight separation

A proof of `WeightSeparationStatement`. The rational-function identity is turned
into a signed identity of root multiplicities at every complex point. Roots of
different degrees have different weights, so each complex point contributes to at
most one degree. The factors over the number field are the published
`algebraicWeightFactor`s, compared at the given embedding with the complex weight
factors by `map_algebraicWeightFactor`.
-/

noncomputable section

open Polynomial
open scoped BigOperators Classical

universe u

namespace Langlands.Cohomology.Weights

/-- A monic complex polynomial is determined by its multiset of roots. -/
theorem eq_of_monic_of_roots_eq {p r : ℂ[X]} (hp : p.Monic) (hr : r.Monic)
    (h : p.roots = r.roots) : p = r :=
  calc p = (p.roots.map fun a => X - C a).prod :=
        (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp
          IsAlgClosed.card_roots_eq_natDegree).symm
    _ = (r.roots.map fun a => X - C a).prod := by rw [h]
    _ = r := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hr
          IsAlgClosed.card_roots_eq_natDegree

/-- Monic complex polynomials with equal nonzero powers are equal. -/
theorem eq_of_monic_of_pow_eq_pow {p r : ℂ[X]} (hp : p.Monic) (hr : r.Monic)
    {n : ℕ} (hn : n ≠ 0) (h : p ^ n = r ^ n) : p = r := by
  apply eq_of_monic_of_roots_eq hp hr
  have hroots : n • p.roots = n • r.roots := by
    rw [← roots_pow, ← roots_pow, h]
  refine Multiset.ext' fun z => ?_
  have hz := congrArg (Multiset.count z) hroots
  rw [Multiset.count_nsmul, Multiset.count_nsmul] at hz
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn) hz

/-- Root multiplicities add over a finite product of monic polynomials. -/
theorem count_roots_prod_of_monic {ι : Type*} (s : Finset ι) (f : ι → ℂ[X])
    (hf : ∀ i ∈ s, (f i).Monic) (z : ℂ) :
    (∏ i ∈ s, f i).roots.count z = ∑ i ∈ s, (f i).roots.count z := by
  rw [roots_prod f s (monic_prod_of_monic s f hf).ne_zero, Multiset.count_bind]
  rfl

/-- The alternating product as a quotient of the even-degree product by the
odd-degree product. -/
theorem alternatingPolynomial_eq_div {K : Type*} [Field K] (d : ℕ)
    (H : Fin (2 * d + 1) → K[X]) :
    alternatingPolynomial d H =
      algebraMap K[X] (RatFunc K)
          (∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) => Even i.val), H i) /
        algebraMap K[X] (RatFunc K)
          (∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) => ¬ Even i.val), H i) := by
  unfold alternatingPolynomial
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun i : Fin (2 * d + 1) => Even i.val),
    map_prod, map_prod, div_eq_mul_inv, ← Finset.prod_inv_distrib]
  congr 1
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.mp hi).2.neg_one_pow, zpow_one]
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [(Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hi).2).neg_one_pow, zpow_neg_one]

/-- The signed root-multiplicity identity at every complex point, deduced from
the rational-function identity. -/
theorem alternatingPolynomial_signed_count_roots {d : ℕ} {a : ℤ} {R : ℂ[X]} (hR : R.Monic)
    {H : Fin (2 * d + 1) → ℂ[X]} (hH : ∀ i, (H i).Monic)
    (h : alternatingPolynomial d H = algebraMap ℂ[X] (RatFunc ℂ) R ^ a) (z : ℂ) :
    ∑ i, (-1 : ℤ) ^ i.val * ((H i).roots.count z : ℤ) = a * (R.roots.count z : ℤ) := by
  set E := ∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) => Even i.val), H i with hE
  set O := ∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) => ¬ Even i.val), H i
    with hO
  have hEm : E.Monic := monic_prod_of_monic _ _ fun i _ => hH i
  have hOm : O.Monic := monic_prod_of_monic _ _ fun i _ => hH i
  have hsum : ∑ i, (-1 : ℤ) ^ i.val * ((H i).roots.count z : ℤ) =
      (E.roots.count z : ℤ) - (O.roots.count z : ℤ) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i : Fin (2 * d + 1) => Even i.val),
      hE, hO, count_roots_prod_of_monic _ _ (fun i _ => hH i),
      count_roots_prod_of_monic _ _ (fun i _ => hH i)]
    push_cast
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [(Finset.mem_filter.mp hi).2.neg_one_pow, one_mul]
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [(Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hi).2).neg_one_pow, neg_one_mul]
  rw [hsum]
  rw [alternatingPolynomial_eq_div] at h
  have hO0 : algebraMap ℂ[X] (RatFunc ℂ) O ≠ 0 := RatFunc.algebraMap_ne_zero hOm.ne_zero
  have hRn0 : algebraMap ℂ[X] (RatFunc ℂ) (R ^ a.natAbs) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (hR.pow _).ne_zero
  rcases Int.natAbs_eq a with ha | ha
  · have hpoly : E = R ^ a.natAbs * O := by
      apply RatFunc.algebraMap_injective ℂ
      rw [map_mul, map_pow, ← zpow_natCast, ← ha, ← h, div_mul_cancel₀ _ hO0]
    rw [hpoly, roots_mul ((hR.pow _).mul hOm).ne_zero, roots_pow, Multiset.count_add,
      Multiset.count_nsmul]
    conv_rhs => rw [ha]
    push_cast
    ring
  · have hpoly : E * R ^ a.natAbs = O := by
      apply RatFunc.algebraMap_injective ℂ
      rw [ha, zpow_neg, zpow_natCast, ← map_pow, div_eq_iff hO0] at h
      rw [map_mul, h, mul_comm _ (algebraMap ℂ[X] (RatFunc ℂ) (R ^ a.natAbs)),
        ← mul_assoc, mul_inv_cancel₀ hRn0, one_mul]
    rw [← hpoly, roots_mul (hEm.mul (hR.pow _)).ne_zero, roots_pow, Multiset.count_add,
      Multiset.count_nsmul]
    conv_rhs => rw [ha]
    push_cast
    ring

/-- Two cohomological degrees whose weights agree at one complex value coincide. -/
theorem fin_eq_of_hasComplexWeight {d q : ℕ} (hq : 1 < q) {w : ℤ}
    {i j : Fin (2 * d + 1)} {z : ℂ}
    (hi : HasComplexWeight q ((i.val : ℤ) + w) z)
    (hj : HasComplexWeight q ((j.val : ℤ) + w) z) : i = j := by
  have h := hi.unique hq hj
  exact Fin.ext (by omega)

/-- Proof of the algebraic weight-separation statement. -/
theorem weightSeparationStatement : WeightSeparationStatement.{u} := by
  intro L _ _ ι d q w a P H hq hPm hPdeg hH hid
  have hHm : ∀ i, (H i).Monic := fun i => (hH i).1
  have hHw : ∀ i, ∀ z ∈ (H i).roots, HasComplexWeight q ((i.val : ℤ) + w) z :=
    fun i z hz => ((hH i).2 z hz).hasComplexWeight
  have hPιm : (P.map ι).Monic := hPm.map ι
  have hsigned := alternatingPolynomial_signed_count_roots hPιm hHm hid
  -- At a root of `H j`, only the degree `j` contributes to the signed identity.
  have hat : ∀ j z, z ∈ (H j).roots →
      (-1 : ℤ) ^ j.val * ((H j).roots.count z : ℤ) =
        a * ((P.map ι).roots.count z : ℤ) := by
    intro j z hz
    rw [← hsigned z, Finset.sum_eq_single j]
    · intro i _ hij
      rw [Multiset.count_eq_zero.mpr fun hzi =>
        hij (fin_eq_of_hasComplexWeight hq (hHw i z hzi) (hHw j z hz)),
        Nat.cast_zero, mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  -- Away from all roots of the `H i`, the right side vanishes.
  have haway : ∀ z, (∀ j, z ∉ (H j).roots) → a * ((P.map ι).roots.count z : ℤ) = 0 := by
    intro z hz
    rw [← hsigned z]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Multiset.count_eq_zero.mpr (hz i), Nat.cast_zero, mul_zero]
  have hsign_ne : ∀ j : Fin (2 * d + 1), (-1 : ℤ) ^ j.val ≠ 0 :=
    fun j => pow_ne_zero _ (by norm_num)
  -- With `a ≠ 0`, every root of `P` at `ι` is a root of some `H j`.
  have hcover : a ≠ 0 → ∀ z ∈ (P.map ι).roots, ∃ j, z ∈ (H j).roots := by
    intro ha z hz
    by_contra hnot
    push Not at hnot
    have h0 := haway z hnot
    have hc : ((P.map ι).roots.count z : ℤ) ≠ 0 := by
      exact_mod_cast (Multiset.count_pos.mpr hz).ne'
    exact mul_ne_zero ha hc h0
  refine ⟨⟨fun ha => ?_, fun ⟨i, hi⟩ ha => ?_⟩, fun ha => ?_⟩
  · -- A nonzero exponent forces a root of some `H j`.
    have hdeg : 0 < (P.map ι).degree := by
      rw [degree_eq_natDegree hPιm.ne_zero, natDegree_map]
      exact_mod_cast hPdeg
    obtain ⟨z, hz⟩ := Complex.exists_root hdeg
    have hzr : z ∈ (P.map ι).roots := (mem_roots hPιm.ne_zero).mpr hz
    obtain ⟨j, hj⟩ := hcover ha z hzr
    refine ⟨j, ?_⟩
    rw [← IsAlgClosed.card_roots_eq_natDegree]
    exact Multiset.card_pos_iff_exists_mem.mpr ⟨z, hj⟩
  · -- If `a = 0`, no `H i` has a root, so each has degree zero.
    have hdeg : 0 < (H i).degree := by
      rw [degree_eq_natDegree (hHm i).ne_zero]
      exact_mod_cast hi
    obtain ⟨z, hz⟩ := Complex.exists_root hdeg
    have hzr : z ∈ (H i).roots := (mem_roots (hHm i).ne_zero).mpr hz
    have h0 := hat i z hzr
    rw [ha, zero_mul] at h0
    have hc : ((H i).roots.count z : ℤ) ≠ 0 := by
      exact_mod_cast (Multiset.count_pos.mpr hzr).ne'
    exact mul_ne_zero (hsign_ne i) hc h0
  · -- The case `a ≠ 0`.
    set n := a.natAbs with hn
    have hn0 : n ≠ 0 := Int.natAbs_ne_zero.mpr ha
    -- Multiplicity and sign at a root of `H j`.
    have hmult : ∀ j z, z ∈ (H j).roots →
        (H j).roots.count z = n * (P.map ι).roots.count z ∧ 0 < (-1 : ℤ) ^ j.val * a := by
      intro j z hz
      have h := hat j z hz
      have hc : 0 < (H j).roots.count z := Multiset.count_pos.mpr hz
      constructor
      · have h' := congrArg Int.natAbs h
        rwa [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg,
          Int.natAbs_one, one_pow, one_mul, Int.natAbs_natCast, Int.natAbs_natCast] at h'
      · have hsq : (-1 : ℤ) ^ j.val * (-1 : ℤ) ^ j.val = 1 := by
          rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
        have h2 : ((H j).roots.count z : ℤ) =
            ((-1 : ℤ) ^ j.val * a) * ((P.map ι).roots.count z : ℤ) := by
          rw [mul_assoc, ← h, ← mul_assoc, hsq, one_mul]
        by_contra hneg
        push Not at hneg
        have hle : ((-1 : ℤ) ^ j.val * a) * ((P.map ι).roots.count z : ℤ) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hneg (Nat.cast_nonneg _)
        have hc' : (0 : ℤ) < ((H j).roots.count z : ℤ) := by exact_mod_cast hc
        linarith
    have hProots : ∀ z ∈ (P.map ι).roots, ∃ v : ℤ, IsWeilNumber q v z := by
      intro z hz
      obtain ⟨j, hj⟩ := hcover ha z hz
      exact ⟨_, (hH j).2 z hj⟩
    -- The candidate factors over `L`.
    let Q : Fin (2 * d + 1) → L[X] := fun j => algebraicWeightFactor q ((j.val : ℤ) + w) P
    have hQmap : ∀ j, (Q j).map ι = complexWeightFactor q ((j.val : ℤ) + w) (P.map ι) :=
      fun j => map_algebraicWeightFactor hq _ hPm ι ι hProots
    have hQpure : ∀ j, IsPurePolynomial q ((j.val : ℤ) + w) (Q j) :=
      fun j => algebraicWeightFactor_isPure q _ P
    have hmapinj : Function.Injective (Polynomial.map ι) :=
      Polynomial.map_injective ι ι.injective
    -- Each `H j` is the `n`-th power of the weight factor.
    have hHQ : ∀ j, H j = (Q j).map ι ^ n := by
      intro j
      apply eq_of_monic_of_roots_eq (hHm j) (((hQpure j).1.map ι).pow n)
      rw [roots_pow, hQmap, roots_complexWeightFactor]
      refine Multiset.ext' fun z => ?_
      rw [Multiset.count_nsmul]
      by_cases hz : z ∈ (H j).roots
      · rw [Multiset.count_filter_of_pos (hHw j z hz)]
        exact (hmult j z hz).1
      · rw [Multiset.count_eq_zero.mpr hz]
        by_cases hzw : HasComplexWeight q ((j.val : ℤ) + w) z
        · rw [Multiset.count_filter_of_pos hzw]
          have hzP : z ∉ (P.map ι).roots := by
            intro hzP
            obtain ⟨k, hk⟩ := hcover ha z hzP
            have hkj : k = j := fin_eq_of_hasComplexWeight hq (hHw k z hk) hzw
            exact hz (hkj ▸ hk)
          rw [Multiset.count_eq_zero.mpr hzP, mul_zero]
        · rw [Multiset.count_filter_of_neg hzw, mul_zero]
    -- Vanishing factors in the wrong parity.
    have hQone : ∀ j, (-1 : ℤ) ^ j.val * a < 0 → Q j = 1 := by
      intro j hj
      apply hmapinj
      rw [hQmap, Polynomial.map_one]
      refine complexWeightFactor_eq_one fun z hz hzw => ?_
      obtain ⟨k, hk⟩ := hcover ha z hz
      have hkj : k = j := fin_eq_of_hasComplexWeight hq (hHw k z hk) hzw
      have hpos := (hmult k z hk).2
      rw [hkj] at hpos
      exact absurd hj (not_lt.mpr hpos.le)
    -- The factors multiply to `P`.
    have hprod : (∏ j, Q j) = P := by
      apply hmapinj
      rw [Polynomial.map_prod]
      apply eq_of_monic_of_roots_eq
        (monic_prod_of_monic _ _ fun j _ => (hQpure j).1.map ι) hPιm
      refine Multiset.ext' fun z => ?_
      rw [count_roots_prod_of_monic _ _ fun j _ => (hQpure j).1.map ι]
      simp only [hQmap, roots_complexWeightFactor]
      by_cases hz : z ∈ (P.map ι).roots
      · obtain ⟨k, hk⟩ := hcover ha z hz
        rw [Finset.sum_eq_single k]
        · exact Multiset.count_filter_of_pos (hHw k z hk)
        · intro j _ hjk
          refine Multiset.count_filter_of_neg fun hzw => hjk ?_
          exact fin_eq_of_hasComplexWeight hq hzw (hHw k z hk)
        · intro hk'
          exact absurd (Finset.mem_univ k) hk'
      · rw [Multiset.count_eq_zero.mpr hz]
        refine Finset.sum_eq_zero fun j _ => ?_
        exact Multiset.count_eq_zero.mpr fun h => hz (Multiset.mem_of_mem_filter h)
    refine ⟨Q, ⟨hprod, fun j => ⟨hQpure j, hHQ j, hQone j⟩⟩, ?_⟩
    -- Uniqueness: `n`-th roots of monic complex polynomials are unique.
    rintro Q' ⟨_, hQ'⟩
    funext j
    apply hmapinj
    exact eq_of_monic_of_pow_eq_pow ((hQ' j).1.1.map ι) ((hQpure j).1.map ι) hn0
      (((hQ' j).2.1).symm.trans (hHQ j))

end Langlands.Cohomology.Weights
