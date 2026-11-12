import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Int.Basic

/-!
# An irreducibility criterion for integer polynomials

Two facts about multivariate polynomials used in the proof of Tadić's Proposition 3.8:

* over a domain, the factors of a nonzero weighted homogeneous polynomial are weighted
  homogeneous (`isWeightedHomogeneous_left_of_mul`);
* a weighted homogeneous `Q ∈ ℤ[σ]` with positive weights is irreducible when a monomial
  `X_{s 0} ⋯ X_{s (n-1)}` of equal-weight variables occurs with coefficient one, every
  monomial of `Q` has degree at most one in each `X_{s j}`, and for every pair of adjacent
  indices `k, k+1` some monomial of `Q` omits `X_{s k}, X_{s (k+1)}`, contains all other
  `X_{s j}`, and has no submonomial free of the `X_{s j}` of weight `w (s j)`
  (`irreducible_of_adjacent`).
-/

noncomputable section

namespace Langlands.Classification.TadicRectanglePrime

open MvPolynomial Finsupp

/-! ### Factors of weighted homogeneous polynomials -/

section Weighted

variable {σ R : Type*} [CommRing R] (w : σ → ℕ)

/-- The substitution `X_i ↦ t^(w i) X_i` into polynomials in `t` over `MvPolynomial σ R`;
the coefficient of `t^k` is the weighted homogeneous component of weight `k`. -/
def weightSubst : MvPolynomial σ R →+* Polynomial (MvPolynomial σ R) :=
  eval₂Hom (Polynomial.C.comp C) fun i => Polynomial.monomial (w i) (X i)

theorem weightSubst_monomial_one (μ : σ →₀ ℕ) :
    weightSubst (R := R) w (monomial μ 1) =
      Polynomial.monomial (weight w μ) (monomial μ 1) := by
  induction μ using Finsupp.induction with
  | zero => simp [weightSubst]
  | single_add i k μ _ _ ih =>
    have h : monomial (single i k + μ) (1 : R) = X i ^ k * monomial μ 1 := by
      rw [X_pow_eq_monomial, monomial_mul_monomial, one_mul]
    have hX : weightSubst (R := R) w (X i) = Polynomial.monomial (w i) (X i) :=
      eval₂Hom_X' _ _ _
    rw [h, map_mul, map_pow, ih, hX, Polynomial.monomial_pow, Polynomial.monomial_mul_monomial]
    congr 1
    rw [map_add, weight_single, smul_eq_mul, mul_comm]

theorem weightSubst_monomial (μ : σ →₀ ℕ) (c : R) :
    weightSubst w (monomial μ c) = Polynomial.monomial (weight w μ) (monomial μ c) := by
  have h : monomial μ c = C c * monomial μ 1 := by rw [C_mul_monomial, mul_one]
  have hC : weightSubst (R := R) w (C c) = Polynomial.C (C c) := eval₂Hom_C _ _ _
  rw [h, map_mul, weightSubst_monomial_one, hC, Polynomial.C_mul_monomial]

theorem coeff_coeff_weightSubst (φ : MvPolynomial σ R) (k : ℕ) (ν : σ →₀ ℕ) :
    ((weightSubst w φ).coeff k).coeff ν = if weight w ν = k then φ.coeff ν else 0 := by
  classical
  induction φ using MvPolynomial.induction_on' with
  | monomial μ c =>
    rw [weightSubst_monomial, Polynomial.coeff_monomial]
    by_cases hμ : μ = ν
    · subst hμ
      split_ifs <;> simp_all
    · rw [coeff_monomial, ite_eq_right hμ]
      split_ifs <;> simp [coeff_monomial, hμ]
  | add p q hp hq =>
    rw [map_add, Polynomial.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    split_ifs <;> simp

theorem coeff_weightSubst_ne_zero {φ : MvPolynomial σ R} {μ : σ →₀ ℕ} (h : φ.coeff μ ≠ 0) :
    (weightSubst w φ).coeff (weight w μ) ≠ 0 := by
  intro h0
  have := coeff_coeff_weightSubst w φ (weight w μ) μ
  rw [h0, ite_eq_left rfl] at this
  exact h (by simpa using this.symm)

theorem weightSubst_ne_zero {φ : MvPolynomial σ R} (h : φ ≠ 0) : weightSubst w φ ≠ 0 := by
  obtain ⟨μ, hμ⟩ := exists_coeff_ne_zero h
  intro h0
  exact coeff_weightSubst_ne_zero w hμ (by rw [h0, Polynomial.coeff_zero])

/-- Over a domain, a left factor of a nonzero weighted homogeneous polynomial is weighted
homogeneous. -/
theorem isWeightedHomogeneous_left_of_mul [IsDomain R] {P₁ P₂ : MvPolynomial σ R} {W : ℕ}
    (h : IsWeightedHomogeneous w (P₁ * P₂) W) (h₁ : P₁ ≠ 0) (h₂ : P₂ ≠ 0) :
    IsWeightedHomogeneous w P₁ (weightSubst w P₁).natDegree := by
  have hA := weightSubst_ne_zero w h₁
  have hB := weightSubst_ne_zero w h₂
  have hAB : weightSubst w (P₁ * P₂) = weightSubst w P₁ * weightSubst w P₂ := map_mul _ _ _
  have hQ : ∀ k, k ≠ W → (weightSubst w (P₁ * P₂)).coeff k = 0 := by
    intro k hk
    ext ν
    rw [coeff_coeff_weightSubst]
    split_ifs with hν
    · by_contra hc
      exact hk (hν.symm.trans (h (by simpa using hc)))
    · simp
  have hprod : weightSubst w P₁ * weightSubst w P₂ ≠ 0 := mul_ne_zero hA hB
  have hdeg : (weightSubst w P₁ * weightSubst w P₂).natDegree ≤ W := by
    rw [← hAB]
    exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun k hk => hQ k (by omega)
  have htr : W ≤ (weightSubst w P₁ * weightSubst w P₂).natTrailingDegree := by
    rw [← hAB]
    exact Polynomial.le_natTrailingDegree (by rw [hAB]; exact hprod)
      fun k hk => hQ k (by omega)
  rw [Polynomial.natDegree_mul hA hB] at hdeg
  rw [Polynomial.natTrailingDegree_mul hA hB] at htr
  have e1 := Polynomial.natTrailingDegree_le_natDegree (weightSubst w P₁)
  have e2 := Polynomial.natTrailingDegree_le_natDegree (weightSubst w P₂)
  intro ν hν
  have h1 := Polynomial.le_natDegree_of_ne_zero (coeff_weightSubst_ne_zero w hν)
  have h2 := Polynomial.natTrailingDegree_le_of_ne_zero (coeff_weightSubst_ne_zero w hν)
  change weight w ν = _
  omega

end Weighted

/-! ### The irreducibility criterion -/

section Criterion

variable {σ R : Type*}

theorem exists_split_of_coeff_mul_ne_zero [CommRing R] {P₁ P₂ : MvPolynomial σ R}
    {μ : σ →₀ ℕ} (h : (P₁ * P₂).coeff μ ≠ 0) :
    ∃ β γ, β + γ = μ ∧ P₁.coeff β ≠ 0 ∧ P₂.coeff γ ≠ 0 := by
  classical
  rw [coeff_mul] at h
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨x.1, x.2, Finset.mem_antidiagonal.mp hx, left_ne_zero_of_mul hne,
    right_ne_zero_of_mul hne⟩

variable (s : ℕ → σ) (n : ℕ)

theorem sum_single_apply_of_mem (hs : ∀ i < n, ∀ j < n, s i = s j → i = j)
    {t : Finset ℕ} (ht : t ⊆ Finset.range n) {j : ℕ} (hj : j < n) :
    (∑ i ∈ t, single (s i) (1 : ℕ)) (s j) = if j ∈ t then 1 else 0 := by
  classical
  rw [Finsupp.finsetSum_apply]
  split_ifs with hjt
  · rw [Finset.sum_eq_single_of_mem j hjt]
    · exact single_eq_same
    · intro i hi hij
      refine single_eq_of_ne fun h => hij ?_
      exact hs i (Finset.mem_range.mp (ht hi)) j hj h.symm
  · refine Finset.sum_eq_zero fun i hi => single_eq_of_ne fun h => ?_
    have := hs i (Finset.mem_range.mp (ht hi)) j hj h.symm
    exact hjt (this ▸ hi)

theorem sum_single_apply_of_not_mem {t : Finset ℕ} {x : σ} (hx : ∀ i ∈ t, s i ≠ x) :
    (∑ i ∈ t, single (s i) (1 : ℕ)) x = 0 := by
  rw [Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero fun i hi => single_eq_of_ne (hx i hi).symm

theorem weight_sum_single (w : σ → ℕ) {D : ℕ} (hD : ∀ j < n, w (s j) = D)
    {t : Finset ℕ} (ht : t ⊆ Finset.range n) :
    weight w (∑ i ∈ t, single (s i) (1 : ℕ)) = t.card * D := by
  rw [map_sum]
  rw [Finset.sum_congr rfl fun i hi => by
    rw [weight_single, one_smul, hD i (Finset.mem_range.mp (ht hi))]]
  rw [Finset.sum_const, smul_eq_mul]

/-- **Irreducibility criterion.** Let `Q ∈ ℤ[σ]` be weighted homogeneous for positive
weights `w`, and let `s 0, …, s (n-1)` be distinct variables of a common weight `D`, with
`n > 0`. Suppose the monomial `X_{s 0} ⋯ X_{s (n-1)}` has coefficient one in `Q`, every
monomial of `Q` has degree at most one in each `X_{s j}`, and for every `k` with
`k + 1 < n` some monomial `μ` of `Q` omits `X_{s k}` and `X_{s (k+1)}`, contains every
other `X_{s j}` once, and has no submonomial of weight `D` free of the `X_{s j}`. Then
`Q` is irreducible. -/
theorem irreducible_of_adjacent (w : σ → ℕ) (hw : ∀ i, 0 < w i) {Q : MvPolynomial σ ℤ}
    {W : ℕ} (hQ : IsWeightedHomogeneous w Q W) (hn : 0 < n)
    (hs : ∀ i < n, ∀ j < n, s i = s j → i = j) {D : ℕ} (hD : ∀ j < n, w (s j) = D)
    (h0 : Q.coeff (∑ j ∈ Finset.range n, single (s j) 1) = 1)
    (h1 : ∀ μ, Q.coeff μ ≠ 0 → ∀ j < n, μ (s j) ≤ 1)
    (h2 : ∀ k, k + 1 < n → ∃ μ, Q.coeff μ ≠ 0 ∧ μ (s k) = 0 ∧ μ (s (k + 1)) = 0 ∧
      (∀ j < n, j ≠ k → j ≠ k + 1 → μ (s j) = 1) ∧
      ∀ ν ≤ μ, (∀ j < n, ν (s j) = 0) → weight w ν ≠ D) :
    Irreducible Q := by
  classical
  set e₀ : σ →₀ ℕ := ∑ j ∈ Finset.range n, single (s j) 1 with he₀
  have hQ0 : Q ≠ 0 := by
    intro h
    simp [h] at h0
  have he₀s : ∀ j < n, e₀ (s j) = 1 := fun j hj => by
    rw [he₀, sum_single_apply_of_mem s n hs subset_rfl hj, ite_eq_left (Finset.mem_range.mpr hj)]
  have hdQ : ∀ j < n, degreeOf (s j) Q = 1 := by
    intro j hj
    refine le_antisymm (degreeOf_le_iff.mpr fun μ hμ => h1 μ (MvPolynomial.mem_support_iff.mp hμ) j hj) ?_
    have := monomial_le_degreeOf (s j) (MvPolynomial.mem_support_iff.mpr (by rw [h0]; exact one_ne_zero) :
      e₀ ∈ Q.support)
    rwa [he₀s j hj] at this
  -- The analysis of a factorization `Q = P₁ * P₂`.
  have key : ∀ P₁ P₂ : MvPolynomial σ ℤ, Q = P₁ * P₂ →
      ((∀ j < n, degreeOf (s j) P₁ = 0) → IsUnit P₁) ∧
      (∀ k, k + 1 < n → degreeOf (s k) P₁ = 1 → degreeOf (s (k + 1)) P₁ = 0 → False) := by
    intro P₁ P₂ hQe
    have hP₁ : P₁ ≠ 0 := by rintro rfl; rw [zero_mul] at hQe; exact hQ0 hQe
    have hP₂ : P₂ ≠ 0 := by rintro rfl; rw [mul_zero] at hQe; exact hQ0 hQe
    have hdeg : ∀ j < n, degreeOf (s j) P₁ + degreeOf (s j) P₂ = 1 := by
      intro j hj
      rw [← degreeOf_mul_eq hP₁ hP₂, ← hQe]
      exact hdQ j hj
    have hQ' : IsWeightedHomogeneous w (P₁ * P₂) W := hQe ▸ hQ
    have hhom := isWeightedHomogeneous_left_of_mul (R := ℤ) w hQ' hP₁ hP₂
    set W₁ := (weightSubst w P₁).natDegree
    set p := (Finset.range n).filter fun j => degreeOf (s j) P₁ = 1 with hp
    have hpn : p ⊆ Finset.range n := Finset.filter_subset _ _
    have hmemp : ∀ j < n, (j ∈ p ↔ degreeOf (s j) P₁ = 1) := fun j hj => by
      rw [hp, Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => h.2, fun h => ⟨hj, h⟩⟩
    -- the factorization of the monomial `e₀`
    obtain ⟨β, γ, hβγ, hβ, hγ⟩ := exists_split_of_coeff_mul_ne_zero
      (P₁ := P₁) (P₂ := P₂) (μ := e₀) (by rw [← hQe, h0]; exact one_ne_zero)
    have hβeq : β = ∑ j ∈ p, single (s j) 1 := by
      ext x
      by_cases hx : ∃ j < n, s j = x
      · obtain ⟨j, hj, rfl⟩ := hx
        rw [sum_single_apply_of_mem s n hs hpn hj]
        have e1 := monomial_le_degreeOf (s j) (MvPolynomial.mem_support_iff.mpr hβ)
        have e2 := monomial_le_degreeOf (s j) (MvPolynomial.mem_support_iff.mpr hγ)
        have e3 : β (s j) + γ (s j) = 1 := by
          rw [← Finsupp.add_apply, hβγ, he₀s j hj]
        have e4 := hdeg j hj
        have e5 := hmemp j hj
        split_ifs with hjp
        · have := e5.mp hjp
          omega
        · have : degreeOf (s j) P₁ ≠ 1 := fun h => hjp (e5.mpr h)
          omega
      · push Not at hx
        have hle : β x ≤ e₀ x := by
          rw [← hβγ, Finsupp.add_apply]
          exact Nat.le_add_right _ _
        rw [he₀, sum_single_apply_of_not_mem s fun i hi => hx i (Finset.mem_range.mp hi)] at hle
        rw [sum_single_apply_of_not_mem s fun i hi => hx i (Finset.mem_range.mp (hpn hi))]
        omega
    have hW₁ : W₁ = p.card * D := by
      rw [← hhom hβ, hβeq, weight_sum_single s n w hD hpn]
    refine ⟨fun hall => ?_, fun k hk hk1 hk0 => ?_⟩
    · -- no variable `X_{s j}` occurs in `P₁`: it is a constant
      have hpe : p = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun j hj => ?_
        have hjn := Finset.mem_range.mp (hpn hj)
        have := (hmemp j hjn).mp hj
        rw [hall j hjn] at this
        exact zero_ne_one this
      rw [hpe, Finset.card_empty, zero_mul] at hW₁
      have hc : P₁ = C (P₁.coeff 0) := by
        ext μ
        rw [coeff_C]
        split_ifs with hμ
        · subst hμ
          rfl
        · by_contra hne
          have hw0 := hhom hne
          rw [hW₁] at hw0
          refine hμ (Finsupp.ext fun i => ?_)
          have := le_weight w (hw i).ne' μ
          rw [Finsupp.coe_zero, Pi.zero_apply]
          change weight w μ = 0 at hw0
          omega
      have hunit : P₁.coeff 0 * P₂.coeff e₀ = 1 := by
        rw [← coeff_C_mul, ← hc, ← hQe, h0]
      rw [hc]
      exact (IsUnit.of_mul_eq_one _ hunit).map C
    · -- an adjacent pair separated by the factorization
      obtain ⟨μ, hμ, hμk, hμk1, hμj, hμν⟩ := h2 k hk
      obtain ⟨β', γ', hβγ', hβ', hγ'⟩ := exists_split_of_coeff_mul_ne_zero
        (P₁ := P₁) (P₂ := P₂) (μ := μ) (by rw [← hQe]; exact hμ)
      have hkp : k ∈ p := (hmemp k (by omega)).mpr hk1
      set E := ∑ j ∈ p.erase k, single (s j) (1 : ℕ) with hE
      have hEn : p.erase k ⊆ Finset.range n := (Finset.erase_subset k p).trans hpn
      have hβ's : ∀ j < n, β' (s j) = if j ∈ p.erase k then 1 else 0 := by
        intro j hj
        have e1 := monomial_le_degreeOf (s j) (MvPolynomial.mem_support_iff.mpr hβ')
        have e2 := monomial_le_degreeOf (s j) (MvPolynomial.mem_support_iff.mpr hγ')
        have e3 : β' (s j) + γ' (s j) = μ (s j) := by
          rw [← Finsupp.add_apply, hβγ']
        have e4 := hdeg j hj
        have e5 := hmemp j hj
        simp only [Finset.mem_erase]
        by_cases hjk : j = k
        · subst hjk
          rw [hμk] at e3
          simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte]
          omega
        by_cases hjk1 : j = k + 1
        · subst hjk1
          rw [hμk1] at e3
          have : k + 1 ∉ p := fun h => by rw [(hmemp _ hj).mp h] at hk0; exact one_ne_zero hk0
          simp only [this, and_false, ↓reduceIte]
          omega
        rw [hμj j hj hjk hjk1] at e3
        split_ifs with hjp
        · have := e5.mp hjp.2
          omega
        · have : degreeOf (s j) P₁ ≠ 1 := fun h => hjp ⟨hjk, e5.mpr h⟩
          omega
      have hEβ : E ≤ β' := by
        intro x
        by_cases hx : ∃ j < n, s j = x
        · obtain ⟨j, hj, rfl⟩ := hx
          rw [hE, sum_single_apply_of_mem s n hs hEn hj, hβ's j hj]
        · push Not at hx
          rw [hE, sum_single_apply_of_not_mem s fun i hi => hx i (Finset.mem_range.mp (hEn hi))]
          exact Nat.zero_le _
      set ν := β' - E with hν
      have hνμ : ν ≤ μ := tsub_le_self.trans (hβγ' ▸ le_self_add)
      have hνs : ∀ j < n, ν (s j) = 0 := by
        intro j hj
        rw [hν, Finsupp.tsub_apply, hE, sum_single_apply_of_mem s n hs hEn hj, hβ's j hj]
        exact Nat.sub_self _
      have hwt : weight w β' = weight w ν + weight w E := by
        rw [← map_add, hν, tsub_add_cancel_of_le hEβ]
      rw [hhom hβ', hW₁, hE, weight_sum_single s n w hD hEn, Finset.card_erase_of_mem hkp] at hwt
      have hcard : 0 < p.card := Finset.card_pos.mpr ⟨k, hkp⟩
      refine hμν ν hνμ hνs ?_
      have : (p.card - 1) * D + D = p.card * D := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hcard]
      omega
  refine ⟨fun hu => ?_, fun P₁ P₂ hQe => ?_⟩
  · obtain ⟨Q', hQ'⟩ := isUnit_iff_exists_inv.mp hu
    have hQ'0 : Q' ≠ 0 := by rintro rfl; rw [mul_zero] at hQ'; exact zero_ne_one hQ'
    have := degreeOf_mul_eq (n := s 0) hQ0 hQ'0
    rw [hQ', ← C_1, degreeOf_C, hdQ 0 hn] at this
    omega
  · have hP₁ : P₁ ≠ 0 := by rintro rfl; rw [zero_mul] at hQe; exact hQ0 hQe
    have hP₂ : P₂ ≠ 0 := by rintro rfl; rw [mul_zero] at hQe; exact hQ0 hQe
    have hdeg : ∀ j < n, degreeOf (s j) P₁ + degreeOf (s j) P₂ = 1 := by
      intro j hj
      rw [← degreeOf_mul_eq hP₁ hP₂, ← hQe]
      exact hdQ j hj
    have hQe' : Q = P₂ * P₁ := by rw [hQe, mul_comm]
    by_cases hall0 : ∀ j < n, degreeOf (s j) P₁ = 0
    · exact Or.inl ((key P₁ P₂ hQe).1 hall0)
    by_cases hall1 : ∀ j < n, degreeOf (s j) P₁ = 1
    · refine Or.inr ((key P₂ P₁ hQe').1 fun j hj => ?_)
      have := hdeg j hj
      rw [hall1 j hj] at this
      omega
    exfalso
    push Not at hall0 hall1
    obtain ⟨j₀, hj₀, hj₀'⟩ := hall0
    obtain ⟨j₁, hj₁, hj₁'⟩ := hall1
    have hadj : ∃ k, k + 1 < n ∧ degreeOf (s k) P₁ ≠ degreeOf (s (k + 1)) P₁ := by
      by_contra hcon
      push Not at hcon
      have hconst : ∀ j < n, degreeOf (s j) P₁ = degreeOf (s 0) P₁ := by
        intro j
        induction j with
        | zero => intro _; rfl
        | succ j ih => intro hj; rw [← hcon j hj, ih (by omega)]
      rw [hconst j₀ hj₀] at hj₀'
      rw [hconst j₁ hj₁] at hj₁'
      exact hj₁' (by have := hdeg 0 hn; omega)
    obtain ⟨k, hk, hne⟩ := hadj
    have e1 := hdeg k (by omega)
    have e2 := hdeg (k + 1) hk
    by_cases hk1 : degreeOf (s k) P₁ = 1
    · exact (key P₁ P₂ hQe).2 k hk hk1 (by omega)
    · exact (key P₂ P₁ hQe').2 k hk (by omega) (by omega)

/-- Under the hypotheses of `irreducible_of_adjacent`, `Q` is a prime element of the
unique factorization domain `ℤ[σ]`. -/
theorem prime_of_adjacent (w : σ → ℕ) (hw : ∀ i, 0 < w i) {Q : MvPolynomial σ ℤ}
    {W : ℕ} (hQ : IsWeightedHomogeneous w Q W) (hn : 0 < n)
    (hs : ∀ i < n, ∀ j < n, s i = s j → i = j) {D : ℕ} (hD : ∀ j < n, w (s j) = D)
    (h0 : Q.coeff (∑ j ∈ Finset.range n, single (s j) 1) = 1)
    (h1 : ∀ μ, Q.coeff μ ≠ 0 → ∀ j < n, μ (s j) ≤ 1)
    (h2 : ∀ k, k + 1 < n → ∃ μ, Q.coeff μ ≠ 0 ∧ μ (s k) = 0 ∧ μ (s (k + 1)) = 0 ∧
      (∀ j < n, j ≠ k → j ≠ k + 1 → μ (s j) = 1) ∧
      ∀ ν ≤ μ, (∀ j < n, ν (s j) = 0) → weight w ν ≠ D) :
    Prime Q :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (irreducible_of_adjacent s n w hw hQ hn hs hD h0 h1 h2)

end Criterion

end Langlands.Classification.TadicRectanglePrime
