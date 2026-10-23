import Mathlib.Data.Sym.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # Unordered nonzero complex eigenvalues and their matrix invariants -/

noncomputable section

open scoped BigOperators
open Polynomial

namespace Langlands.Unramified

/-- An unordered list of exactly `n` nonzero complex eigenvalues, with multiplicities. -/
abbrev Eigenvalues (n : ℕ) := Sym ℂˣ n

namespace Eigenvalues

variable {n m : ℕ}

/-- Forget the ordering of a tuple, retaining every multiplicity. -/
def ofTuple (z : Fin n → ℂˣ) : Eigenvalues n :=
  ⟨(List.ofFn z : Multiset ℂˣ), by simp⟩

theorem ofTuple_reindex (z : Fin n → ℂˣ) (e : Equiv.Perm (Fin n)) :
    ofTuple (z ∘ e) = ofTuple z := by
  apply Sym.ext
  change (List.ofFn (z ∘ e) : Multiset ℂˣ) = (List.ofFn z : Multiset ℂˣ)
  rw [← Fin.univ_val_map, ← Fin.univ_val_map, ← Multiset.map_map,
    Multiset.map_univ_val_equiv]

@[simp] theorem ofTuple_cons (z : ℂˣ) (t : Fin n → ℂˣ) :
    ofTuple (Fin.cons z t) = Sym.cons z (ofTuple t) := by
  apply Sym.ext
  change (List.ofFn (Fin.cons z t) : Multiset ℂˣ) = z ::ₘ (List.ofFn t : Multiset ℂˣ)
  simp

theorem ofTuple_surjective (n : ℕ) :
    Function.Surjective (ofTuple : (Fin n → ℂˣ) → Eigenvalues n) := by
  induction n with
  | zero =>
      intro s
      refine ⟨Fin.elim0, ?_⟩
      exact (Sym.eq_nil_of_card_zero _).trans (Sym.eq_nil_of_card_zero s).symm
  | succ n ih =>
      intro s
      obtain ⟨z, t, rfl⟩ := Sym.exists_eq_cons_of_succ s
      obtain ⟨v, rfl⟩ := ih t
      exact ⟨Fin.cons z v, ofTuple_cons z v⟩

/-- Concatenate two spectra, allowing different ranks. -/
def directSum (s : Eigenvalues n) (t : Eigenvalues m) : Eigenvalues (n + m) :=
  s.append t

@[simp] theorem ofTuple_append (z : Fin n → ℂˣ) (w : Fin m → ℂˣ) :
    ofTuple (Fin.append z w) = directSum (ofTuple z) (ofTuple w) := by
  apply Sym.ext
  change (List.ofFn (Fin.append z w) : Multiset ℂˣ) =
    (List.ofFn z : Multiset ℂˣ) + (List.ofFn w : Multiset ℂˣ)
  simp [List.ofFn_fin_append]

/-- Raise each eigenvalue to a natural power. -/
def power (s : Eigenvalues n) (k : ℕ) : Eigenvalues n :=
  s.map (fun z => z ^ k)

@[simp] theorem power_ofTuple (z : Fin n → ℂˣ) (k : ℕ) :
    power (ofTuple z) k = ofTuple (fun i => z i ^ k) := by
  apply Sym.ext
  simp [power, ofTuple, List.map_ofFn, Function.comp_def]

@[simp] theorem power_one (s : Eigenvalues n) : power s 1 = s := by
  simp [power]

theorem power_power (s : Eigenvalues n) (a b : ℕ) :
    power (power s a) b = power s (a * b) := by
  simp [power, Sym.map_map, pow_mul]

theorem power_directSum (s : Eigenvalues n) (t : Eigenvalues m) (k : ℕ) :
    power (directSum s t) k = directSum (power s k) (power t k) := by
  apply Sym.ext
  simp [power, directSum, Sym.coe_map, Sym.coe_append]

/-- The sum of the `k`th powers, including `k = 0` as the rank. -/
def powerTrace (s : Eigenvalues n) (k : ℕ) : ℂ :=
  ((s : Multiset ℂˣ).map (fun z : ℂˣ => (z : ℂ) ^ k)).sum

/-- The Euler denominator polynomial, with constant coefficient one. -/
def eulerPolynomial (s : Eigenvalues n) : ℂ[X] :=
  ((s : Multiset ℂˣ).map (fun z : ℂˣ => 1 - C (z : ℂ) * X)).prod

@[simp] theorem powerTrace_ofTuple (z : Fin n → ℂˣ) (k : ℕ) :
    powerTrace (ofTuple z) k = ∑ i, (z i : ℂ) ^ k := by
  simp [powerTrace, ofTuple, List.map_ofFn, Function.comp_def, Fin.sum_ofFn]

@[simp] theorem eulerPolynomial_ofTuple (z : Fin n → ℂˣ) :
    eulerPolynomial (ofTuple z) = ∏ i, (1 - C (z i : ℂ) * X) := by
  simp [eulerPolynomial, ofTuple, List.map_ofFn, Function.comp_def, Fin.prod_ofFn]

@[simp] theorem powerTrace_zero (s : Eigenvalues n) : powerTrace s 0 = n := by
  obtain ⟨z, rfl⟩ := ofTuple_surjective n s
  simp

theorem powerTrace_power (s : Eigenvalues n) (a b : ℕ) :
    powerTrace (power s a) b = powerTrace s (a * b) := by
  simp [powerTrace, power, Sym.coe_map, Multiset.map_map, pow_mul]

@[simp] theorem powerTrace_directSum (s : Eigenvalues n) (t : Eigenvalues m) (k : ℕ) :
    powerTrace (directSum s t) k = powerTrace s k + powerTrace t k := by
  simp [powerTrace, directSum, Sym.coe_append]

@[simp] theorem eulerPolynomial_directSum (s : Eigenvalues n) (t : Eigenvalues m) :
    eulerPolynomial (directSum s t) = eulerPolynomial s * eulerPolynomial t := by
  simp [eulerPolynomial, directSum, Sym.coe_append]

@[simp] theorem eulerPolynomial_eval_zero (s : Eigenvalues n) :
    (eulerPolynomial s).eval 0 = 1 := by
  obtain ⟨z, rfl⟩ := ofTuple_surjective n s
  simp [Polynomial.eval_prod]

theorem eulerPolynomial_ne_zero (s : Eigenvalues n) : eulerPolynomial s ≠ 0 := by
  intro h
  have := eulerPolynomial_eval_zero s
  simp [h] at this

@[simp] theorem eulerPolynomial_natDegree (s : Eigenvalues n) :
    (eulerPolynomial s).natDegree = n := by
  obtain ⟨z, rfl⟩ := ofTuple_surjective n s
  have hd (u : ℂˣ) : (1 - C (u : ℂ) * X).natDegree = 1 := by
    rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt]
    · simp [Polynomial.natDegree_C_mul u.ne_zero]
    · simp [Polynomial.natDegree_C_mul u.ne_zero]
  rw [eulerPolynomial_ofTuple, Polynomial.natDegree_prod]
  · simp_rw [hd]
    simp
  · intro i _ h
    have := hd (z i)
    simp [h] at this

/-- The actual invertible diagonal matrix for an ordered tuple. -/
def diagonal (z : Fin n → ℂˣ) : Matrix.GeneralLinearGroup (Fin n) ℂ where
  val := Matrix.diagonal (fun i => (z i : ℂ))
  inv := Matrix.diagonal (fun i => ((z i)⁻¹ : ℂˣ))
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp

@[simp] theorem diagonal_val (z : Fin n → ℂˣ) :
    (diagonal z : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun i => (z i : ℂ)) := rfl

theorem trace_diagonal_pow (z : Fin n → ℂˣ) (k : ℕ) :
    Matrix.trace ((diagonal z : Matrix (Fin n) (Fin n) ℂ) ^ k) =
      powerTrace (ofTuple z) k := by
  simp [Matrix.diagonal_pow, Matrix.trace_diagonal]

theorem charpolyRev_diagonal (z : Fin n → ℂˣ) :
    (diagonal z : Matrix (Fin n) (Fin n) ℂ).charpolyRev =
      eulerPolynomial (ofTuple z) := by
  rw [Matrix.charpolyRev, eulerPolynomial_ofTuple]
  have h : (1 : Matrix (Fin n) (Fin n) ℂ[X]) -
      (X : ℂ[X]) • (diagonal z : Matrix (Fin n) (Fin n) ℂ).map C =
      Matrix.diagonal (fun i => 1 - C (z i : ℂ) * X) := by
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, diagonal_val,
        Matrix.diagonal_apply, Matrix.one_apply, ite_true, smul_eq_mul]
      rw [mul_comm]
    · simp [hij]
  rw [h, Matrix.det_diagonal]

/-- Every unordered spectrum is realized by an actual invertible complex matrix
with the prescribed Euler polynomial and all natural power traces. -/
theorem exists_matrix (s : Eigenvalues n) :
    ∃ A : Matrix.GeneralLinearGroup (Fin n) ℂ,
      (A : Matrix (Fin n) (Fin n) ℂ).charpolyRev = eulerPolynomial s ∧
      ∀ k : ℕ, Matrix.trace ((A : Matrix (Fin n) (Fin n) ℂ) ^ k) = powerTrace s k := by
  obtain ⟨z, rfl⟩ := ofTuple_surjective n s
  exact ⟨diagonal z, charpolyRev_diagonal z, trace_diagonal_pow z⟩

end Eigenvalues
end Langlands.Unramified
