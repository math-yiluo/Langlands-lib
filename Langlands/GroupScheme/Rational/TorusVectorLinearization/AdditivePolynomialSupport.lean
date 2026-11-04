import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Nat.Choose.Lucas

/-! # Polynomials that are additive on every algebra are `p`-polynomials

Over a commutative ring in which a prime `p` vanishes, a polynomial in finitely many
variables that is additive on every algebra is a finite sum of scalar multiples of
the powers `X j ^ p ^ s`.
-/

noncomputable section

universe u

open Polynomial

namespace Langlands.GroupScheme.RelativeRoot.AdditiveSupport

variable {A : Type u} [CommRing A]

private theorem algebraMap_polynomial_polynomial :
    algebraMap A A[X][X] = (C : A[X] →+* A[X][X]).comp C := by
  ext a
  simp [Polynomial.algebraMap_apply]

/-- For an additive one-variable polynomial, the binomial multiples of its
coefficients vanish strictly inside the range. -/
theorem choose_mul_coeff_eq_zero (q : A[X])
    (hq : ∀ (B : Type u) [CommRing B] [Algebra A B] (x y : B),
      aeval (x + y) q = aeval x q + aeval y q)
    {m i : ℕ} (hi : 0 < i) (him : i < m) :
    (m.choose i : A) * q.coeff m = 0 := by
  have h := hq A[X][X] (C X) X
  have hl : aeval (C X + X : A[X][X]) q = taylor (X : A[X]) (q.map C) := by
    rw [taylor_apply, Polynomial.comp, eval₂_map, aeval_def, add_comm,
      algebraMap_polynomial_polynomial]
  have h1 : aeval (C X : A[X][X]) q = C q := by
    rw [aeval_def, algebraMap_polynomial_polynomial, ← hom_eval₂, eval₂_C_X]
  have h2 : aeval (X : A[X][X]) q = q.map C := by
    rw [aeval_def, algebraMap_polynomial_polynomial]
    rfl
  rw [hl, h1, h2] at h
  have hc := congrArg (fun r : A[X][X] => (r.coeff i).coeff (m - i)) h
  simp only [taylor_coeff, hasseDeriv_map, eval_map, eval₂_C_X, hasseDeriv_coeff,
    Nat.sub_add_cancel him.le, coeff_add, coeff_C, coeff_map,
    ite_eq_right hi.ne', ite_eq_right (Nat.sub_ne_zero_of_lt him), zero_add] at hc
  simpa using hc

variable {p : ℕ} [hp : Fact p.Prime]

/-- An additive one-variable polynomial has no coefficient outside the powers of `p`. -/
theorem coeff_eq_zero_of_additive (hpA : (p : A) = 0) (q : A[X])
    (hq : ∀ (B : Type u) [CommRing B] [Algebra A B] (x y : B),
      aeval (x + y) q = aeval x q + aeval y q)
    {m : ℕ} (hm : ∀ s, m ≠ p ^ s) : q.coeff m = 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · have h := hq A 0 0
    rw [add_zero] at h
    rw [coeff_zero_eq_aeval_zero]
    exact left_eq_add.mp h
  · obtain ⟨i, hi, hmod⟩ : ∃ i ∈ Finset.Icc 1 (m - 1), ¬ m.choose i ≡ 0 [MOD p] := by
      by_contra! h
      exact hm _ (Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat hm0 h)
    rw [Finset.mem_Icc] at hi
    have hmul := choose_mul_coeff_eq_zero q hq (m := m) (i := i) (by omega) (by omega)
    have hcop : Nat.Coprime (m.choose i) p :=
      ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr
        (fun hd => hmod (Nat.modEq_zero_iff_dvd.mpr hd))).symm
    have hb := Nat.gcd_eq_gcd_ab (m.choose i) p
    rw [hcop.gcd_eq_one] at hb
    have hb' := congrArg (Int.cast : ℤ → A) hb
    push_cast at hb'
    rw [hpA, zero_mul, add_zero] at hb'
    calc q.coeff m = ((m.choose i : A) * (Nat.gcdA (m.choose i) p : A)) * q.coeff m := by
          rw [← hb', one_mul]
      _ = (Nat.gcdA (m.choose i) p : A) * ((m.choose i : A) * q.coeff m) := by ring
      _ = 0 := by rw [hmul, mul_zero]

/-- An additive one-variable polynomial is a sum of `p`-power monomials. -/
theorem eq_sum_pow_of_additive (hpA : (p : A) = 0) (q : A[X])
    (hq : ∀ (B : Type u) [CommRing B] [Algebra A B] (x y : B),
      aeval (x + y) q = aeval x q + aeval y q)
    {N : ℕ} (hN : q.natDegree < N) :
    q = ∑ s ∈ Finset.range N, C (q.coeff (p ^ s)) * X ^ (p ^ s) := by
  ext m
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  by_cases hm : ∃ s, m = p ^ s
  · obtain ⟨s, rfl⟩ := hm
    rw [Finset.sum_eq_single s]
    · simp
    · intro t _ hts
      rw [ite_eq_right, mul_zero]
      intro h
      exact hts (Nat.pow_right_injective hp.out.two_le h).symm
    · intro hs
      rw [Finset.mem_range, not_lt] at hs
      rw [coeff_eq_zero_of_natDegree_lt, zero_mul]
      exact hN.trans_le (hs.trans (Nat.lt_pow_self hp.out.one_lt).le)
  · push Not at hm
    rw [coeff_eq_zero_of_additive hpA q hq hm]
    symm
    apply Finset.sum_eq_zero
    intro s _
    rw [ite_eq_right (hm s), mul_zero]

variable {σ : Type} [Fintype σ] [DecidableEq σ]

omit [Fintype σ] [DecidableEq σ] in
private theorem mvAeval_sum (Q : MvPolynomial σ A)
    {B : Type u} [CommRing B] [Algebra A B]
    (hQ : ∀ x y : σ → B, MvPolynomial.aeval (x + y) Q =
      MvPolynomial.aeval x Q + MvPolynomial.aeval y Q)
    {ι : Type*} (s : Finset ι) (f : ι → σ → B) :
    MvPolynomial.aeval (∑ i ∈ s, f i) Q = ∑ i ∈ s, MvPolynomial.aeval (f i) Q := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := hQ 0 0
    rw [add_zero] at h
    simpa using left_eq_add.mp h
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, hQ, ih]

omit [Fintype σ] in
private theorem aeval_single_eq (Q : MvPolynomial σ A) (j : σ)
    {B : Type u} [CommRing B] [Algebra A B] (z : B) :
    aeval z (MvPolynomial.aeval (Pi.single j (X : A[X])) Q) =
      MvPolynomial.aeval (Pi.single j z) Q := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 2
  funext i
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

/-- A polynomial in finitely many variables that is additive on every algebra is a
finite sum of scalar multiples of the powers `X j ^ p ^ s`; the range of exponents
`s` may be any sufficiently long initial segment. -/
theorem MvPolynomial.exists_eq_sum_pow_of_additive (hpA : (p : A) = 0)
    (Q : MvPolynomial σ A)
    (hQ : ∀ (B : Type u) [CommRing B] [Algebra A B] (x y : σ → B),
      MvPolynomial.aeval (x + y) Q = MvPolynomial.aeval x Q + MvPolynomial.aeval y Q) :
    ∃ (N₀ : ℕ) (c : σ → ℕ → A), ∀ N, N₀ ≤ N →
      Q = ∑ j, ∑ s ∈ Finset.range N,
        MvPolynomial.C (c j s) * MvPolynomial.X j ^ (p ^ s) := by
  let q : σ → A[X] := fun j => MvPolynomial.aeval (Pi.single j (X : A[X])) Q
  have hq (j : σ) (B : Type u) [CommRing B] [Algebra A B] (x y : B) :
      aeval (x + y) (q j) = aeval x (q j) + aeval y (q j) := by
    simp only [q, aeval_single_eq, Pi.single_add]
    exact hQ B _ _
  let N := ∑ j, ((q j).natDegree + 1)
  have hN (j : σ) : (q j).natDegree < N :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
      (Finset.single_le_sum (f := fun j => (q j).natDegree + 1)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  refine ⟨N, fun j s => (q j).coeff (p ^ s), fun N' hN' => ?_⟩
  have hsplit : Q = ∑ j, MvPolynomial.aeval
      (Pi.single j (MvPolynomial.X j : MvPolynomial σ A)) Q := by
    rw [← mvAeval_sum Q (hQ _) Finset.univ, Finset.univ_sum_single,
      MvPolynomial.aeval_X_left_apply]
  conv_lhs => rw [hsplit]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← aeval_single_eq Q j]
  change aeval (MvPolynomial.X j) (q j) = _
  conv_lhs => rw [eq_sum_pow_of_additive hpA (q j) (hq j) ((hN j).trans_le hN')]
  simp only [map_sum, map_mul, aeval_C, map_pow, aeval_X, MvPolynomial.algebraMap_eq]

end Langlands.GroupScheme.RelativeRoot.AdditiveSupport
