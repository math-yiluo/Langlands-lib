import Langlands.GroupScheme.IntegralModel.Smoothening.TerminationDilatation
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

/-! # Homogeneous forms in generators of the augmentation ideal

Let `C` be an `R`-algebra with an `R`-point `ε` and augmentation ideal `I`. Let `x i ∈ I` be
elements that span `I` modulo `I²`. Then every element of `I ^ j` is a homogeneous form of degree
`j` in the `x i` modulo `I ^ (j + 1)`.

Suppose moreover that no nonzero homogeneous form of degree `n` in the `x i` lies in `I ^ (n + 1)`
(graded independence), and let `ϖ` be a prime element of the domain `R`. Then:

* `ϖ c ∈ I ^ j` implies `c ∈ I ^ j`;
* a homogeneous form of degree `n` in the `x i` lying in `I ^ (n + 1) + ϖ C` has all its
  coefficients divisible by `ϖ`;
* if `c ^ 2 ∈ ϖ C`, then `c ∈ I ^ j + ϖ C` for every `j`.

The last statement says that a function whose square vanishes on the special fibre lies in every
power of the augmentation ideal of the special fibre. -/

noncomputable section

open MvPolynomial

namespace Langlands.GroupScheme.IntegralModel.Smoothening.Termination

variable {R : Type*} [CommRing R] {C : Type*} [CommRing C] [Algebra R C] (ε : C →ₐ[R] R)
  {d : ℕ} (x : Fin d → C)

theorem prod_pow_mem_pow (hx : ∀ i, x i ∈ augIdeal ε) (μ : Fin d →₀ ℕ) :
    μ.prod (fun i k => x i ^ k) ∈ augIdeal ε ^ μ.degree := by
  rw [Finsupp.prod, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hx i) _

/-- A homogeneous form of degree `j` in elements of `I` lies in `I ^ j`. -/
theorem aeval_mem_pow (hx : ∀ i, x i ∈ augIdeal ε) {P : MvPolynomial (Fin d) R} {j : ℕ}
    (hP : P.IsHomogeneous j) : aeval x P ∈ augIdeal ε ^ j := by
  rw [P.as_sum, map_sum]
  refine Ideal.sum_mem _ fun μ hμ => ?_
  rw [aeval_monomial]
  have hdeg : μ.degree = j := by
    have := hP (mem_support_iff.mp hμ)
    rw [Finsupp.degree_eq_weight_one]
    exact this
  exact Ideal.mul_mem_left _ _ (hdeg ▸ prod_pow_mem_pow ε x hx μ)

/-- A polynomial whose coefficients are divisible by `ϖ` takes values in `ϖ C`. -/
theorem aeval_mem_span_of_dvd {ϖ : R} {P : MvPolynomial (Fin d) R}
    (hP : ∀ μ, ϖ ∣ P.coeff μ) : aeval x P ∈ Ideal.span {algebraMap R C ϖ} := by
  rw [P.as_sum, map_sum]
  refine Ideal.sum_mem _ fun μ _ => ?_
  rw [aeval_monomial]
  obtain ⟨r, hr⟩ := hP μ
  rw [hr, map_mul, mul_assoc]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

variable {ε x}

/-- **Spanning.** If the `x i` span `I` modulo `I²`, every element of `I ^ j` is a homogeneous
form of degree `j` in the `x i` modulo `I ^ (j + 1)`. -/
theorem exists_isHomogeneous (hx : ∀ i, x i ∈ augIdeal ε)
    (hspan : ∀ y ∈ augIdeal ε, ∃ r : Fin d → R, y - ∑ i, r i • x i ∈ augIdeal ε ^ 2) (j : ℕ) :
    ∀ y ∈ augIdeal ε ^ j, ∃ P : MvPolynomial (Fin d) R,
      P.IsHomogeneous j ∧ y - aeval x P ∈ augIdeal ε ^ (j + 1) := by
  induction j with
  | zero =>
    intro y _
    refine ⟨MvPolynomial.C (ε y), isHomogeneous_C _ _, ?_⟩
    rw [aeval_C, zero_add, pow_one]
    exact sub_algebraMap_mem ε y
  | succ j ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha b hb
      obtain ⟨P, hP, hPa⟩ := ih a ha
      obtain ⟨r, hr⟩ := hspan b hb
      refine ⟨P * ∑ i, MvPolynomial.C (r i) * X i,
        hP.mul (IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X _ _), ?_⟩
      have heq : a * b - aeval x (P * ∑ i, MvPolynomial.C (r i) * X i) =
          (a - aeval x P) * b + aeval x P * (b - ∑ i, r i • x i) := by
        simp only [map_mul, map_sum, aeval_C, aeval_X, Algebra.smul_def]
        ring
      rw [heq]
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_succ _ (j + 1)]
        exact Ideal.mul_mem_mul hPa hb
      · have : augIdeal ε ^ (j + 1 + 1) = augIdeal ε ^ j * augIdeal ε ^ 2 := by
          rw [← pow_add]
        rw [this]
        exact Ideal.mul_mem_mul (aeval_mem_pow ε x hx hP) hr
    · rintro y y' ⟨P, hP, hy⟩ ⟨P', hP', hy'⟩
      refine ⟨P + P', hP.add hP', ?_⟩
      have : y + y' - aeval x (P + P') = (y - aeval x P) + (y' - aeval x P') := by
        rw [map_add]
        ring
      rw [this]
      exact Ideal.add_mem _ hy hy'

section Independent

variable [IsDomain R] (hx : ∀ i, x i ∈ augIdeal ε)
  (hspan : ∀ y ∈ augIdeal ε, ∃ r : Fin d → R, y - ∑ i, r i • x i ∈ augIdeal ε ^ 2)
  (hind : ∀ (n : ℕ) (Q : MvPolynomial (Fin d) R), Q.IsHomogeneous n →
    aeval x Q ∈ augIdeal ε ^ (n + 1) → Q = 0)
include hx hspan hind

/-- **Saturation.** Under graded independence, `ϖ c ∈ I ^ j` implies `c ∈ I ^ j`. -/
theorem mem_pow_of_smul_mem {ϖ : R} (hϖ : ϖ ≠ 0) (j : ℕ) :
    ∀ c : C, ϖ • c ∈ augIdeal ε ^ j → c ∈ augIdeal ε ^ j := by
  induction j with
  | zero =>
    intro c _
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ j ih =>
    intro c hc
    have hcj : c ∈ augIdeal ε ^ j := ih c (Ideal.pow_le_pow_right (Nat.le_succ j) hc)
    obtain ⟨P, hP, hPc⟩ := exists_isHomogeneous hx hspan j c hcj
    have h0 : MvPolynomial.C ϖ * P = 0 := by
      refine hind j _ (hP.C_mul ϖ) ?_
      have : aeval x (MvPolynomial.C ϖ * P) = ϖ • c - algebraMap R C ϖ * (c - aeval x P) := by
        rw [map_mul, aeval_C, Algebra.smul_def]
        ring
      rw [this]
      exact Ideal.sub_mem _ hc (Ideal.mul_mem_left _ _ hPc)
    have hP0 : P = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd (C_eq_zero.mp h) hϖ
      · exact h
    rw [hP0, map_zero, sub_zero] at hPc
    exact hPc

/-- A homogeneous form of degree `n` lying in `I ^ (n + 1) + ϖ C` has all its coefficients
divisible by `ϖ`. -/
theorem dvd_coeff_of_mem_sup {ϖ : R} (hϖ : ϖ ≠ 0) {n : ℕ} {Q : MvPolynomial (Fin d) R}
    (hQ : Q.IsHomogeneous n)
    (h : aeval x Q ∈ augIdeal ε ^ (n + 1) ⊔ Ideal.span {algebraMap R C ϖ}) (μ : Fin d →₀ ℕ) :
    ϖ ∣ Q.coeff μ := by
  obtain ⟨i, hi, p, hp, hip⟩ := Submodule.mem_sup.mp h
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
  have hc : ϖ • c ∈ augIdeal ε ^ n := by
    have : ϖ • c = aeval x Q - i := by
      rw [Algebra.smul_def, ← hip]
      ring
    rw [this]
    exact Ideal.sub_mem _ (aeval_mem_pow ε x hx hQ) (Ideal.pow_le_pow_right (Nat.le_succ n) hi)
  have hcn := mem_pow_of_smul_mem hx hspan hind hϖ n c hc
  obtain ⟨P, hP, hPc⟩ := exists_isHomogeneous hx hspan n c hcn
  have h0 : Q - MvPolynomial.C ϖ * P = 0 := by
    refine hind n _ (hQ.sub (hP.C_mul ϖ)) ?_
    have : aeval x (Q - MvPolynomial.C ϖ * P) = i + algebraMap R C ϖ * (c - aeval x P) := by
      rw [map_sub, map_mul, aeval_C, ← hip]
      ring
    rw [this]
    exact Ideal.add_mem _ hi (Ideal.mul_mem_left _ _ hPc)
  refine ⟨P.coeff μ, ?_⟩
  have := congrArg (fun p : MvPolynomial (Fin d) R => p.coeff μ) h0
  simp only [MvPolynomial.coeff_sub, coeff_C_mul, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero,
    Pi.zero_apply, sub_eq_zero] at this
  exact this

/-- **Square-zero functions on the special fibre.** If `c ^ 2 ∈ ϖ C` for a prime `ϖ`, then
`c ∈ I ^ j + ϖ C` for every `j`. -/
theorem mem_sup_of_sq_mem {ϖ : R} (hϖ : Prime ϖ) {c : C}
    (hc : c ^ 2 ∈ Ideal.span {algebraMap R C ϖ}) (j : ℕ) :
    c ∈ augIdeal ε ^ j ⊔ Ideal.span {algebraMap R C ϖ} := by
  induction j with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_sup_left Submodule.mem_top
  | succ j ih =>
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp ih
    obtain ⟨P, hP, hPa⟩ := exists_isHomogeneous hx hspan j a ha
    -- the square of the leading form lies in `I ^ (2j+1) + ϖ C`
    have hsq : aeval x (P ^ 2) ∈ augIdeal ε ^ (2 * j + 1) ⊔ Ideal.span {algebraMap R C ϖ} := by
      set i := a - aeval x P
      have heq : aeval x (P ^ 2) = ((a + b) ^ 2 - b * (2 * a + b)) - i * (2 * aeval x P + i) := by
        simp only [i, map_pow]
        ring
      rw [heq]
      refine Ideal.sub_mem _ (Ideal.sub_mem _ (Submodule.mem_sup_right hc)
        (Submodule.mem_sup_right (Ideal.mul_mem_right _ _ hb))) (Submodule.mem_sup_left ?_)
      have : augIdeal ε ^ (2 * j + 1) = augIdeal ε ^ (j + 1) * augIdeal ε ^ j := by
        rw [← pow_add]
        ring_nf
      rw [this]
      refine Ideal.mul_mem_mul hPa (Ideal.add_mem _ ?_ (Ideal.pow_le_pow_right (Nat.le_succ j) hPa))
      exact Ideal.mul_mem_left _ _ (aeval_mem_pow ε x hx hP)
    have hdvd2 := dvd_coeff_of_mem_sup hx hspan hind hϖ.ne_zero (hP.pow 2) (by
      rwa [mul_comm j 2])
    -- reduce modulo `ϖ`: the square of the reduction of `P` vanishes
    have hprime : (Ideal.span {ϖ}).IsPrime := (Ideal.span_singleton_prime hϖ.ne_zero).mpr hϖ
    let q : R →+* R ⧸ Ideal.span {ϖ} := Ideal.Quotient.mk _
    have hq2 : map q (P ^ 2) = 0 := by
      refine MvPolynomial.ext _ _ fun μ => ?_
      rw [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply,
        Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact hdvd2 μ
    have hq : map q P = 0 := by
      rw [map_pow] at hq2
      exact pow_eq_zero_iff (two_ne_zero) |>.mp hq2
    have hdvd : ∀ μ, ϖ ∣ P.coeff μ := fun μ => by
      have := congrArg (fun p : MvPolynomial (Fin d) (R ⧸ Ideal.span {ϖ}) => p.coeff μ) hq
      simp only [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at this
      rwa [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
    have hPspan := aeval_mem_span_of_dvd x hdvd
    have : a + b = (a - aeval x P) + (aeval x P + b) := by ring
    rw [this]
    exact Ideal.add_mem _ (Submodule.mem_sup_left hPa)
      (Submodule.mem_sup_right (Ideal.add_mem _ hPspan hb))

end Independent

end Langlands.GroupScheme.IntegralModel.Smoothening.Termination
