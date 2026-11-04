import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Data.Rat.Floor

/-! # Weighted leading terms over a discrete valuation ring

Let `A` be a discrete valuation ring with fraction field `K` and residue field `F`, and
let `w` be a family of positive integer weights. If a point `ξ ∈ K^ι` is not integral but
every member of a family of weighted-homogeneous polynomials of positive degree takes an
integral value at `ξ`, then the leading coefficients of `ξ` form a nonzero point of `F^ι`
at which every reduced polynomial of the family vanishes.
-/

noncomputable section

open MvPolynomial IsLocalRing

namespace Langlands.CommutativeAlgebra

namespace DVRWeightedLeadingTerm

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

/-- Every element of the fraction field is `u * ϖ ^ z` for an integer `z` and an element `u`
of `A` which is zero or a unit. -/
theorem exists_eq_mul_zpow {ϖ : A} (hϖ : Irreducible ϖ) (x : FractionRing A) :
    ∃ (u : A) (z : ℤ), (u = 0 ∨ IsUnit u) ∧
      x = algebraMap A (FractionRing A) u * algebraMap A (FractionRing A) ϖ ^ z := by
  by_cases hx : x = 0
  · exact ⟨0, 0, Or.inl rfl, by simp [hx]⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A x
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hx
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  obtain ⟨m, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hϖK : algebraMap A (FractionRing A) ϖ ≠ 0 :=
    fun h => hϖ.ne_zero (IsFractionRing.to_map_eq_zero_iff.mp h)
  have hvK : algebraMap A (FractionRing A) (v : A) ≠ 0 :=
    fun h => v.ne_zero (IsFractionRing.to_map_eq_zero_iff.mp h)
  refine ⟨((u * v⁻¹ : Aˣ) : A), (n : ℤ) - m, Or.inr (Units.isUnit _), ?_⟩
  rw [zpow_sub₀ hϖK, zpow_natCast, zpow_natCast]
  have huv : algebraMap A (FractionRing A) ((u * v⁻¹ : Aˣ) : A) * algebraMap A _ (v : A) =
      algebraMap A _ (u : A) := by
    rw [← map_mul, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  have hpow : algebraMap A (FractionRing A) ϖ ^ m ≠ 0 := pow_ne_zero _ hϖK
  rw [map_mul, map_mul, map_pow, map_pow, ← huv]
  field_simp

/-- A product of natural powers of integer powers of a nonzero element. -/
theorem prod_zpow_pow {ι K : Type*} [Field K] {π : K} (hπ : π ≠ 0) (s : Finset ι)
    (z : ι → ℤ) (n : ι → ℕ) :
    ∏ i ∈ s, (π ^ z i) ^ n i = π ^ (∑ i ∈ s, (n i : ℤ) * z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ hπ, ← zpow_natCast,
      ← zpow_mul, mul_comm (z j)]

/-- Weighted leading terms: if `ξ` is not integral but each polynomial of `S` is weighted
homogeneous of positive degree and integral at `ξ`, then there is a nonzero point of the
residue field at which every polynomial of `S` vanishes. -/
theorem exists_ne_zero_forall_aeval_eq_zero {ι : Type*} [Fintype ι] (w : ι → ℕ)
    (hw : ∀ i, 0 < w i) (S : Set (MvPolynomial ι A))
    (hS : ∀ f ∈ S, ∃ d : ℕ, 0 < d ∧ f.IsWeightedHomogeneous w d)
    (ξ : ι → FractionRing A)
    (hint : ∀ f ∈ S, aeval ξ f ∈ (algebraMap A (FractionRing A)).range)
    (hξ : ¬ ∀ i, ξ i ∈ (algebraMap A (FractionRing A)).range) :
    ∃ a : ι → ResidueField A, a ≠ 0 ∧ ∀ f ∈ S, aeval a f = 0 := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  choose u z hu hξu using fun i => exists_eq_mul_zpow hϖ (ξ i)
  obtain ⟨π, hπ⟩ : ∃ π, π = algebraMap A (FractionRing A) ϖ := ⟨_, rfl⟩
  simp only [← hπ] at hξu
  have hπ0 : π ≠ 0 := by
    rw [hπ]
    exact fun h => hϖ.ne_zero (IsFractionRing.to_map_eq_zero_iff.mp h)
  let T : Finset ι := Finset.univ.filter fun i => u i ≠ 0
  let r : ι → ℚ := fun i => (-(z i) : ℚ) / w i
  push Not at hξ
  obtain ⟨i0, hi0⟩ := hξ
  have hu0 : u i0 ≠ 0 := by
    intro h
    apply hi0
    rw [hξu i0, h]
    exact ⟨0, by simp⟩
  have hz0 : z i0 < 0 := by
    by_contra h
    push Not at h
    apply hi0
    rw [hξu i0]
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
    exact ⟨u i0 * ϖ ^ n, by rw [hn, zpow_natCast, map_mul, map_pow, hπ]⟩
  have hT : T.Nonempty := ⟨i0, by simp [T, hu0]⟩
  obtain ⟨i1, hi1T, hmax⟩ := Finset.exists_max_image T r hT
  set M := r i1 with hMdef
  have hr0 : 0 < r i0 := by
    have : (0 : ℚ) < w i0 := by exact_mod_cast hw i0
    have hz : (0 : ℚ) < -(z i0 : ℚ) := by
      have : (z i0 : ℚ) < 0 := by exact_mod_cast hz0
      linarith
    exact div_pos hz this
  have hM : 0 < M := lt_of_lt_of_le hr0 (hmax i0 (by simp [T, hu0]))
  have hu1 : u i1 ≠ 0 := by simpa [T] using hi1T
  -- `-z i ≤ M * w i` for every index with `u i ≠ 0`.
  have hbound : ∀ i, u i ≠ 0 → (-(z i) : ℚ) ≤ M * w i := by
    intro i hi
    have hwi : (0 : ℚ) < w i := by exact_mod_cast hw i
    have := hmax i (by simp [T, hi])
    rw [div_le_iff₀ hwi] at this
    simpa [r] using this
  have hstrict : ∀ i, u i ≠ 0 → r i ≠ M → (-(z i) : ℚ) < M * w i := by
    intro i hi hne
    have hwi : (0 : ℚ) < w i := by exact_mod_cast hw i
    have hlt : r i < M := lt_of_le_of_ne (hmax i (by simp [T, hi])) hne
    rw [div_lt_iff₀ hwi] at hlt
    simpa [r] using hlt
  have htight : ∀ i, u i ≠ 0 → r i = M → (-(z i) : ℚ) = M * w i := by
    intro i _ heq
    have hwi : (0 : ℚ) ≠ w i := by exact_mod_cast (hw i).ne
    rw [← heq]
    simp only [r]
    field_simp
  let a : ι → ResidueField A := fun i => if u i ≠ 0 ∧ r i = M then residue A (u i) else 0
  have hunit : ∀ i, u i ≠ 0 → IsUnit (u i) := fun i hi => (hu i).resolve_left hi
  refine ⟨a, ?_, ?_⟩
  · intro h
    have h1 : a i1 = 0 := congr_fun h i1
    simp only [a] at h1
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hu1, rfl⟩)] at h1
    exact ((hunit i1 hu1).map (residue A)).ne_zero h1
  intro f hf
  obtain ⟨d, hd, hhom⟩ := hS f hf
  obtain ⟨b, hb⟩ := hint f hf
  set N : ℤ := Int.ceil (M * d) with hNdef
  have hMd : 0 < M * d := mul_pos hM (by exact_mod_cast hd)
  have hN : 0 < N := Int.ceil_pos.mpr hMd
  -- The integer `-v(ξ^α)` and the exponent of `ϖ` in `ϖ ^ N * ξ ^ α`.
  let s : (ι →₀ ℕ) → ℤ := fun α => ∑ i, (α i : ℤ) * (-(z i))
  let e : (ι →₀ ℕ) → ℕ := fun α => (N - s α).toNat
  -- For a monomial supported where `u ≠ 0`, `s α ≤ M * d ≤ N`.
  have hsle : ∀ α, f.coeff α ≠ 0 → (∀ i, α i ≠ 0 → u i ≠ 0) → (s α : ℚ) ≤ M * d := by
    intro α hα hsupp
    have hwt : ((Finsupp.weight w α : ℕ) : ℚ) = d := by exact_mod_cast hhom hα
    rw [Finsupp.weight_eq_sum] at hwt
    push_cast [smul_eq_mul] at hwt
    rw [← hwt, Finset.mul_sum]
    simp only [s]
    push_cast
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : α i = 0
    · simp [hi]
    · have := hbound i (hsupp i hi)
      have hα0 : (0 : ℚ) ≤ α i := by positivity
      nlinarith
  have hsN : ∀ α, f.coeff α ≠ 0 → (∀ i, α i ≠ 0 → u i ≠ 0) → s α ≤ N := by
    intro α hα hsupp
    have := hsle α hα hsupp
    have hc : M * d ≤ (N : ℚ) := Int.le_ceil _
    exact_mod_cast this.trans hc
  -- The integral element `g` with `g = ϖ ^ N * f(ξ)`.
  let g : A := ∑ α ∈ f.support, f.coeff α * (∏ i, u i ^ α i) * ϖ ^ e α
  have hmono : ∀ α ∈ f.support,
      algebraMap A (FractionRing A) (f.coeff α * (∏ i, u i ^ α i) * ϖ ^ e α) =
        π ^ N * (algebraMap A (FractionRing A) (f.coeff α) * ∏ i, ξ i ^ α i) := by
    intro α hα
    rw [MvPolynomial.mem_support_iff] at hα
    by_cases hsupp : ∀ i, α i ≠ 0 → u i ≠ 0
    · have hξprod : ∏ i, ξ i ^ α i =
          algebraMap A (FractionRing A) (∏ i, u i ^ α i) * π ^ (-(s α)) := by
        simp only [hξu, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
        rw [prod_zpow_pow hπ0]
        congr 2
        simp only [s, mul_neg, Finset.sum_neg_distrib, neg_neg]
      have he : ((e α : ℕ) : ℤ) = N - s α := by
        simp only [e]
        exact Int.toNat_of_nonneg (by linarith [hsN α hα hsupp])
      have : π ^ (e α) = π ^ N * π ^ (-(s α)) := by
        rw [← zpow_natCast, he, ← zpow_add₀ hπ0, sub_eq_add_neg]
      rw [hξprod, map_mul, map_mul, map_pow, ← hπ, this]
      ring
    · push Not at hsupp
      obtain ⟨i, hi, hui⟩ := hsupp
      have h1 : ∏ j, u j ^ α j = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hui, zero_pow hi])
      have h2 : ∏ j, ξ j ^ α j = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i)
          (by rw [hξu i, hui, map_zero, zero_mul, zero_pow hi])
      rw [h1, h2]
      simp
  have hg : algebraMap A (FractionRing A) g = π ^ N * aeval ξ f := by
    rw [aeval_def, eval₂_eq', Finset.mul_sum, map_sum]
    exact Finset.sum_congr rfl hmono
  have hgb : g = ϖ ^ N.toNat * b := by
    apply IsFractionRing.injective A (FractionRing A)
    rw [hg, ← hb, map_mul, map_pow, ← hπ, ← zpow_natCast, Int.toNat_of_nonneg hN.le]
  have hres0 : residue A ϖ = 0 :=
    (residue_eq_zero_iff ϖ).mpr ((mem_maximalIdeal ϖ).mpr (mem_nonunits_iff.mpr hϖ.not_isUnit))
  have hgres : residue A g = 0 := by
    rw [hgb, map_mul, map_pow, hres0, zero_pow (by omega), zero_mul]
  suffices hfin : aeval a f = residue A g by rw [hfin, hgres]
  rw [aeval_def, eval₂_eq', ResidueField.algebraMap_eq]
  simp only [g, map_sum, map_mul, map_prod, map_pow, hres0]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [MvPolynomial.mem_support_iff] at hα
  rw [mul_assoc]
  congr 1
  by_cases htsupp : ∀ i, α i ≠ 0 → u i ≠ 0 ∧ r i = M
  · -- every variable of the monomial is tight: the exponent `e α` vanishes
    have hsupp : ∀ i, α i ≠ 0 → u i ≠ 0 := fun i hi => (htsupp i hi).1
    have hseq : (s α : ℚ) = M * d := by
      have hwt : ((Finsupp.weight w α : ℕ) : ℚ) = d := by exact_mod_cast hhom hα
      rw [Finsupp.weight_eq_sum] at hwt
      push_cast [smul_eq_mul] at hwt
      rw [← hwt, Finset.mul_sum]
      simp only [s]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : α i = 0
      · simp [hi]
      · rw [htight i (htsupp i hi).1 (htsupp i hi).2]
        ring
    have hNs : N = s α := by
      rw [hNdef, ← hseq, Int.ceil_intCast]
    have he : e α = 0 := by simp [e, hNs]
    rw [he, pow_zero, mul_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : α i = 0
    · simp [hi]
    · simp only [a]
      rw [ite_eq_left_of_eq_true _ _ (eq_true (htsupp i hi))]
  · push Not at htsupp
    obtain ⟨i, hi, hti⟩ := htsupp
    have hai : a i = 0 := by
      simp only [a]
      rw [ite_eq_right_of_eq_false _ _ (eq_false ?_)]
      tauto
    have hzero : ∏ j, a j ^ α j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hai, zero_pow hi])
    rw [hzero]
    by_cases hui : u i = 0
    · have : ∏ j, residue A (u j) ^ α j = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hui, map_zero, zero_pow hi])
      rw [this, zero_mul]
    · by_cases hsupp : ∀ j, α j ≠ 0 → u j ≠ 0
      · -- a non-tight variable: the exponent `e α` is positive
        have hlt : (s α : ℚ) < M * d := by
          have hwt : ((Finsupp.weight w α : ℕ) : ℚ) = d := by exact_mod_cast hhom hα
          rw [Finsupp.weight_eq_sum] at hwt
          push_cast [smul_eq_mul] at hwt
          rw [← hwt, Finset.mul_sum]
          simp only [s]
          push_cast
          refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
          · by_cases hj : α j = 0
            · simp [hj]
            · have := hbound j (hsupp j hj)
              have hα0 : (0 : ℚ) ≤ α j := by positivity
              nlinarith
          · have := hstrict i hui (hti hui)
            have hα0 : (0 : ℚ) < α i := by exact_mod_cast Nat.pos_of_ne_zero hi
            nlinarith
        have hc : M * d ≤ (N : ℚ) := Int.le_ceil _
        have hsN' : s α < N := by exact_mod_cast hlt.trans_le hc
        have he : e α ≠ 0 := by
          simp only [e]
          omega
        rw [zero_pow he, mul_zero]
      · push Not at hsupp
        obtain ⟨j, hj, huj⟩ := hsupp
        have : ∏ j, residue A (u j) ^ α j = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ j) (by rw [huj, map_zero, zero_pow hj])
        rw [this, zero_mul]

end DVRWeightedLeadingTerm

end Langlands.CommutativeAlgebra
