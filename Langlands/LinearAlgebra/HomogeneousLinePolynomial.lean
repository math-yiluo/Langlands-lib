import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Fin.Tuple.Basic

/-! # A monic polynomial from a normalized binary homogeneous law -/

noncomputable section

namespace Langlands.LinearAlgebra

open scoped BigOperators

variable {R : Type*} [CommSemiring R]

/-- Set the second variable to one and keep the first variable as a polynomial. -/
def binaryLinePolynomial (P : MvPolynomial (Fin 2) R) : Polynomial R :=
  ∑ m ∈ P.support, Polynomial.C (P.coeff m) * Polynomial.X ^ m 0

theorem binaryLinePolynomial_eval (P : MvPolynomial (Fin 2) R) (x : R) :
    (binaryLinePolynomial P).eval x = MvPolynomial.eval ![x, 1] P := by
  simp [binaryLinePolynomial, Polynomial.eval_finsetSum,
    MvPolynomial.eval_eq', Fin.prod_univ_two]

private theorem binary_exponents {P : MvPolynomial (Fin 2) R} {d : ℕ}
    (hP : P.IsHomogeneous d) {m : Fin 2 →₀ ℕ} (hm : m ∈ P.support) :
    m 0 + m 1 = d := by
  have h := hP (MvPolynomial.mem_support_iff.mp hm)
  change m.weight (fun _ => 1) = d at h
  rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum, Fin.sum_univ_two] at h
  exact h

theorem binaryLinePolynomial_natDegree_le {P : MvPolynomial (Fin 2) R} {d : ℕ}
    (hP : P.IsHomogeneous d) : (binaryLinePolynomial P).natDegree ≤ d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
    (Nat.le.intro (binary_exponents hP hm))

theorem binaryLinePolynomial_topCoeff {P : MvPolynomial (Fin 2) R} {d : ℕ}
    (hP : P.IsHomogeneous d) :
    (binaryLinePolynomial P).coeff d = MvPolynomial.eval ![1, 0] P := by
  simp only [binaryLinePolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow, MvPolynomial.eval_eq',
    Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_pow, one_mul]
  apply Finset.sum_congr rfl
  intro m hm
  have hmd := binary_exponents hP hm
  by_cases h0 : m 0 = d
  · have h1 : m 1 = 0 := by omega
    simp [h0, h1]
  · have h1 : m 1 ≠ 0 := by omega
    simp [h1, Ne.symm h0]

/-- Normalization in the first coordinate gives monicity and exact degree. -/
theorem binaryLinePolynomial_monic_natDegree [Nontrivial R]
    {P : MvPolynomial (Fin 2) R} {d : ℕ} (hP : P.IsHomogeneous d)
    (h1 : MvPolynomial.eval ![1, 0] P = 1) :
    (binaryLinePolynomial P).Monic ∧ (binaryLinePolynomial P).natDegree = d := by
  have hc : (binaryLinePolynomial P).coeff d = 1 :=
    (binaryLinePolynomial_topCoeff hP).trans h1
  have hd := binaryLinePolynomial_natDegree_le hP
  exact ⟨Polynomial.monic_of_natDegree_le_of_coeff_eq_one d hd hc,
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hd (hc ▸ one_ne_zero)⟩

/-- A normalized homogeneous law on a two-dimensional span gives its monic
restriction to the affine line. -/
theorem exists_monic_linePolynomial {E : Type*} [AddCommMonoid E] [Module R E]
    [Nontrivial R] (δ : E → R) (v w : E) (d : ℕ)
    (h : ∃ P : MvPolynomial (Fin 2) R, P.IsHomogeneous d ∧
      ∀ x : Fin 2 → R, MvPolynomial.eval x P = δ (x 0 • v + x 1 • w))
    (hv : δ v = 1) :
    ∃ Q : Polynomial R, Q.Monic ∧ Q.natDegree = d ∧
      ∀ x : R, Q.eval x = δ (x • v + w) := by
  obtain ⟨P, hP, he⟩ := h
  have h1 : MvPolynomial.eval ![1, 0] P = 1 := by
    simpa using (he ![1, 0]).trans (by simpa using hv)
  obtain ⟨hm, hd⟩ := binaryLinePolynomial_monic_natDegree hP h1
  refine ⟨binaryLinePolynomial P, hm, hd, ?_⟩
  intro x
  rw [binaryLinePolynomial_eval, he]
  simp

end Langlands.LinearAlgebra
