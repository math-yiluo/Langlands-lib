import Langlands.LinearAlgebra.HomogeneousPolynomialExponent
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.CommRing

/-! # Determinants of elementary homogeneous polynomial substitutions -/

noncomputable section

universe u w

namespace Langlands.LinearAlgebra.HomogeneousPolynomial

open MvPolynomial

variable {σ : Type w} {R : Type u} [CommRing R]

/-- Generatorwise congruence of a polynomial substitution implies congruence on
every polynomial. -/
theorem dvd_aeval_sub (a : MvPolynomial σ R) (z : σ → MvPolynomial σ R)
    (hz : ∀ j, a ∣ z j - X j) (p : MvPolynomial σ R) : a ∣ aeval z p - p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp only [aeval_C, algebraMap_eq, sub_self, dvd_zero]
  | add p q hp hq =>
    rw [map_add, add_sub_add_comm]
    exact dvd_add hp hq
  | mul_X p j hp =>
    have heq : aeval z (p * X j) - p * X j =
        aeval z p * (z j - X j) + (aeval z p - p) * X j := by
      rw [map_mul, aeval_X]
      ring
    rw [heq]
    exact dvd_add (dvd_mul_of_dvd_right (hz j) _) (dvd_mul_of_dvd_left hp _)

/-- If substitution fixes a variable and is congruent to the identity modulo it,
its difference from the identity gains one power of that variable. -/
theorem X_pow_succ_dvd_aeval_sub (i : σ) (z : σ → MvPolynomial σ R)
    (hz : ∀ j, X i ∣ z j - X j) (hi : z i = X i)
    (k : ℕ) {p : MvPolynomial σ R} (hp : X i ^ k ∣ p) :
    X i ^ (k + 1) ∣ aeval z p - p := by
  obtain ⟨q, rfl⟩ := hp
  obtain ⟨r, hr⟩ := dvd_aeval_sub (X i) z hz q
  refine ⟨r, ?_⟩
  rw [map_mul, map_pow, aeval_X, hi]
  calc
    X i ^ k * aeval z q - X i ^ k * q = X i ^ k * (aeval z q - q) := by ring
    _ = X i ^ k * (X i * r) := by rw [hr]
    _ = X i ^ (k + 1) * r := by rw [pow_succ, mul_assoc]

theorem X_pow_dvd_monomial (i : σ) (e : σ →₀ ℕ) :
    (X i : MvPolynomial σ R) ^ e i ∣ monomial e (1 : R) := by
  rw [X_pow_eq_monomial]
  exact monomial_dvd_monomial.mpr
    ⟨Or.inr (Finsupp.single_le_iff.mpr le_rfl), dvd_rfl⟩

theorem coeff_eq_zero_of_X_pow_dvd (i : σ) (k : ℕ) {p : MvPolynomial σ R}
    (hp : X i ^ k ∣ p) (e : σ →₀ ℕ) (he : e i < k) : p.coeff e = 0 := by
  classical
  obtain ⟨q, rfl⟩ := hp
  rw [X_pow_eq_monomial, coeff_monomial_mul']
  have hnot : ¬Finsupp.single i k ≤ e := by
    simpa only [Finsupp.single_le_iff, not_le] using he
  exact ite_eq_right hnot

section Matrix

variable [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
theorem column_add (M N : Matrix σ σ R) (j : σ) :
    column (M + N) j = column M j + column N j := by
  simp only [column, Matrix.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem column_transvection (i j : σ) (c : R) (s : σ) :
    column (Matrix.transvection i j c) s =
      X s + if s = j then C c * X i else 0 := by
  classical
  rw [Matrix.transvection, column_add, column_one]
  congr 1
  by_cases hs : s = j
  · subst s
    simp [column, Matrix.single_apply, apply_ite, ite_mul]
  · simp [column, hs, Ne.symm hs]

/-- At exponents that do not increase in the fixed variable, a transvection acts
as the identity on monomial coefficients. -/
theorem representation_transvection_le (i j : σ) (hij : i ≠ j) (c : R) (d : ℕ)
    (e f : MonomialIndex σ d) (h : e.val i ≤ f.val i) :
    representation (Matrix.transvection i j c) d e f =
      (1 : Matrix (MonomialIndex σ d) (MonomialIndex σ d) R) e f := by
  have hz : ∀ s, X i ∣ column (Matrix.transvection i j c) s - X s := by
    intro s
    rw [column_transvection]
    by_cases hs : s = j <;> simp [hs]
  have hi : column (Matrix.transvection i j c) i = X i := by
    simp only [column_transvection, ite_eq_right hij, add_zero]
  have hdvd := X_pow_succ_dvd_aeval_sub i _ hz hi (f.val i)
    (X_pow_dvd_monomial (R := R) i f.val)
  have hcoeff := coeff_eq_zero_of_X_pow_dvd i (f.val i + 1) hdvd e.val (by omega)
  rw [coeff_sub, sub_eq_zero] at hcoeff
  rw [representation_apply, hcoeff]
  simp [coeff_monomial, Matrix.one_apply, Subtype.ext_iff, eq_comm]

/-- Homogeneous polynomial substitution by a transvection has determinant one
over every commutative coefficient ring. -/
theorem det_representation_transvection (i j : σ) (hij : i ≠ j) (c : R) (d : ℕ) :
    (representation (Matrix.transvection i j c) d).det = 1 := by
  classical
  let b : MonomialIndex σ d → OrderDual ℕ := fun e => e.val i
  have htri : Matrix.BlockTriangular (representation (Matrix.transvection i j c) d) b := by
    intro e f h
    have hlt : e.val i < f.val i := h
    rw [representation_transvection_le i j hij c d e f (Nat.le_of_lt hlt)]
    have hef : e ≠ f := by
      intro h'
      subst f
      exact (Nat.lt_irrefl _ hlt)
    simp [hef]
  have hblock : ∀ k, (representation (Matrix.transvection i j c) d).toSquareBlock b k = 1 := by
    intro k
    ext e f
    change representation (Matrix.transvection i j c) d e.val f.val = _
    have heq : e.val.val i = f.val.val i := e.property.trans f.property.symm
    rw [representation_transvection_le i j hij c d e.val f.val (Nat.le_of_eq heq)]
    by_cases hef : e = f
    · subst f
      simp
    · have hval : e.val ≠ f.val := fun h' => hef (Subtype.ext h')
      simp [hef, hval]
  rw [htri.det]
  simp only [hblock, Matrix.det_one, Finset.prod_const_one]

end Matrix

section Field

variable {K : Type u} [Field K] [Fintype σ] [DecidableEq σ]

/-- The homogeneous determinant power formula for all matrices over a field,
including singular matrices. -/
theorem det_representation_field (M : Matrix σ σ K) (d : ℕ) :
    (representation M d).det = M.det ^ exponent σ d := by
  apply Matrix.diagonal_transvection_induction
    (fun N => (representation N d).det = N.det ^ exponent σ d) M
  · intro a _
    exact det_representation_diagonal_pow a d
  · intro t
    rw [Matrix.TransvectionStruct.toMatrix, det_representation_transvection _ _ t.hij,
      Matrix.det_transvection_of_ne _ _ t.hij, one_pow]
  · intro A B hA hB
    rw [representation_mul, Matrix.det_mul, hA, hB, Matrix.det_mul, mul_pow]

end Field

end Langlands.LinearAlgebra.HomogeneousPolynomial
