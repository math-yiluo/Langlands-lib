import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Choose.Cast

/-! # Separately polynomial functions on `ℕ³` along quadratic lines -/

open Polynomial Finset

noncomputable section

namespace Langlands.Algebra.SeparatelyPolynomial

/-- The coefficient of `X ^ i` in the Lagrange basis polynomial at the node `s` for the nodes
`0, 1, …, D`. -/
def lagrangeWeight (D i s : ℕ) : ℚ :=
  (Lagrange.basis (range (D + 1)) (fun t : ℕ => (t : ℚ)) s).coeff i

/-- Every coefficient of a rational polynomial of natural degree at most `D` is a fixed linear
combination of its values at `0, 1, …, D`. -/
theorem coeff_eq_sum_lagrangeWeight {D : ℕ} {p : ℚ[X]} (hp : p.natDegree ≤ D) (i : ℕ) :
    p.coeff i = ∑ s ∈ range (D + 1), lagrangeWeight D i s * p.eval (s : ℚ) := by
  have hinj : Set.InjOn (fun t : ℕ => (t : ℚ)) (range (D + 1) : Set ℕ) :=
    fun a _ b _ h => by simpa using h
  have hdeg : p.degree < #(range (D + 1)) := by
    rw [card_range]
    exact degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hp)
  conv_lhs => rw [Lagrange.eq_interpolate hinj hdeg]
  rw [Lagrange.interpolate_apply, finsetSum_coeff]
  refine sum_congr rfl fun s _ => ?_
  rw [coeff_C_mul, lagrangeWeight, mul_comm]

/-- A function on `ℕ` given by a polynomial of natural degree at most `D` is the polynomial
whose coefficients are the Lagrange combinations of its values at `0, 1, …, D`. -/
theorem eq_sum_of_eval {D : ℕ} {f : ℕ → ℚ} {p : ℚ[X]} (hp : p.natDegree ≤ D)
    (hf : ∀ x : ℕ, f x = p.eval (x : ℚ)) (x : ℕ) :
    f x = ∑ i ∈ range (D + 1),
      (x : ℚ) ^ i * ∑ s ∈ range (D + 1), lagrangeWeight D i s * f s := by
  rw [hf, eval_eq_sum_range' (Nat.lt_succ_of_le hp)]
  refine sum_congr rfl fun i _ => ?_
  rw [coeff_eq_sum_lagrangeWeight hp, mul_comm]
  simp_rw [hf]

/-- Finite rational combinations of functions given by polynomials of natural degree at most
`D` are again given by such a polynomial. -/
theorem exists_eval_sum {D : ℕ} {ι : Type*} (t : Finset ι) (c : ι → ℚ) (f : ι → ℕ → ℚ)
    (hf : ∀ j, ∃ p : ℚ[X], p.natDegree ≤ D ∧ ∀ x : ℕ, f j x = p.eval (x : ℚ)) :
    ∃ p : ℚ[X], p.natDegree ≤ D ∧ ∀ x : ℕ, ∑ j ∈ t, c j * f j x = p.eval (x : ℚ) := by
  choose P hPdeg hP using hf
  refine ⟨∑ j ∈ t, C (c j) * P j, ?_, fun x => ?_⟩
  · exact natDegree_sum_le_of_forall_le _ _ fun j _ =>
      (natDegree_C_mul_le _ _).trans (hPdeg j)
  · rw [eval_finsetSum]
    exact sum_congr rfl fun j _ => by rw [eval_mul, eval_C, hP]

/-- A function on `ℕ³` that is polynomial of natural degree at most `D` in each variable
separately is a polynomial function with monomials of degree at most `D` in each variable. -/
theorem exists_eq_sum_monomial {D : ℕ} (G : ℕ → ℕ → ℕ → ℚ)
    (hx : ∀ y z, ∃ p : ℚ[X], p.natDegree ≤ D ∧ ∀ x : ℕ, G x y z = p.eval (x : ℚ))
    (hy : ∀ x z, ∃ p : ℚ[X], p.natDegree ≤ D ∧ ∀ y : ℕ, G x y z = p.eval (y : ℚ))
    (hz : ∀ x y, ∃ p : ℚ[X], p.natDegree ≤ D ∧ ∀ z : ℕ, G x y z = p.eval (z : ℚ)) :
    ∃ c : ℕ → ℕ → ℕ → ℚ, ∀ x y z : ℕ, G x y z =
      ∑ i ∈ range (D + 1), ∑ j ∈ range (D + 1), ∑ l ∈ range (D + 1),
        c i j l * (x : ℚ) ^ i * (y : ℚ) ^ j * (z : ℚ) ^ l := by
  let w := lagrangeWeight D
  let a : ℕ → ℕ → ℕ → ℚ := fun i y z => ∑ s ∈ range (D + 1), w i s * G s y z
  let b : ℕ → ℕ → ℕ → ℚ := fun i j z => ∑ t ∈ range (D + 1), w j t * a i t z
  let c : ℕ → ℕ → ℕ → ℚ := fun i j l => ∑ r ∈ range (D + 1), w l r * b i j r
  have hG : ∀ x y z, G x y z = ∑ i ∈ range (D + 1), (x : ℚ) ^ i * a i y z := by
    intro x y z
    obtain ⟨p, hp, hpe⟩ := hx y z
    exact eq_sum_of_eval (f := fun x => G x y z) hp hpe x
  have ha : ∀ i y z, a i y z = ∑ j ∈ range (D + 1), (y : ℚ) ^ j * b i j z := by
    intro i y z
    obtain ⟨p, hp, hpe⟩ := exists_eval_sum (range (D + 1)) (w i) (fun s y => G s y z)
      (fun s => hy s z)
    exact eq_sum_of_eval (f := fun y => a i y z) hp hpe y
  have hb : ∀ i j z, b i j z = ∑ l ∈ range (D + 1), (z : ℚ) ^ l * c i j l := by
    intro i j z
    have ha' : ∀ t, ∃ p : ℚ[X], p.natDegree ≤ D ∧ ∀ z : ℕ, a i t z = p.eval (z : ℚ) :=
      fun t => exists_eval_sum (range (D + 1)) (w i) (fun s z => G s t z) (fun s => hz s t)
    obtain ⟨p, hp, hpe⟩ := exists_eval_sum (range (D + 1)) (w j) (fun t z => a i t z) ha'
    exact eq_sum_of_eval (f := fun z => b i j z) hp hpe z
  refine ⟨c, fun x y z => ?_⟩
  rw [hG]
  refine sum_congr rfl fun i _ => ?_
  rw [ha, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [hb, mul_sum, mul_sum]
  refine sum_congr rfl fun l _ => ?_
  ring

/-- Let `G` be a function on `ℕ³` that is polynomial of bounded natural degree in each variable
separately. Suppose that for each `n` the rational polynomial `E n` evaluates at every natural
`m` to `G (m * C(n, 2)) (m * n) m`. Then for every `g` the `g`-th coefficient of `E n` is a
polynomial in `n` of natural degree at most `2 * g`. -/
theorem exists_coeff_eq_eval_of_quadraticLine {D : ℕ} (G : ℕ → ℕ → ℕ → ℚ)
    (hx : ∀ y z, ∃ p : ℚ[X], p.natDegree ≤ D ∧ ∀ x : ℕ, G x y z = p.eval (x : ℚ))
    (hy : ∀ x z, ∃ p : ℚ[X], p.natDegree ≤ D ∧ ∀ y : ℕ, G x y z = p.eval (y : ℚ))
    (hz : ∀ x y, ∃ p : ℚ[X], p.natDegree ≤ D ∧ ∀ z : ℕ, G x y z = p.eval (z : ℚ))
    (E : ℕ → ℚ[X])
    (hE : ∀ n m : ℕ, (E n).eval (m : ℚ) = G (m * n.choose 2) (m * n) m) (g : ℕ) :
    ∃ R : ℚ[X], R.natDegree ≤ 2 * g ∧ ∀ n : ℕ, (E n).coeff g = R.eval (n : ℚ) := by
  obtain ⟨c, hc⟩ := exists_eq_sum_monomial G hx hy hz
  let A : ℚ[X] := C (1 / 2 : ℚ) * (X * (X - 1))
  have hA : A.natDegree ≤ 2 := by
    refine (natDegree_C_mul_le _ _).trans ((natDegree_mul_le).trans ?_)
    have h1 : (X - 1 : ℚ[X]).natDegree ≤ 1 := by
      rw [← C_1, natDegree_X_sub_C]
    have h2 : (X : ℚ[X]).natDegree ≤ 1 := natDegree_X_le
    omega
  have hAeval : ∀ n : ℕ, A.eval (n : ℚ) = (n.choose 2 : ℚ) := by
    intro n
    rw [Nat.cast_choose_two]
    simp only [A, eval_mul, eval_C, eval_X, eval_sub, eval_one]
    ring
  let T : ℕ → ℚ[X] := fun n => ∑ i ∈ range (D + 1), ∑ j ∈ range (D + 1),
    ∑ l ∈ range (D + 1), C (c i j l * (n.choose 2 : ℚ) ^ i * (n : ℚ) ^ j) * X ^ (i + j + l)
  have hET : ∀ n, E n = T n := by
    intro n
    apply eq_of_infinite_eval_eq
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective Nat.cast_injective)
    rintro _ ⟨m, rfl⟩
    simp only [Set.mem_ofPred_eq]
    rw [hE, hc]
    simp only [T, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun l _ => ?_
    push_cast
    ring
  let R : ℚ[X] := ∑ i ∈ range (D + 1), ∑ j ∈ range (D + 1), ∑ l ∈ range (D + 1),
    C (if g = i + j + l then c i j l else 0) * A ^ i * X ^ j
  refine ⟨R, ?_, fun n => ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun i _ =>
      natDegree_sum_le_of_forall_le _ _ fun j _ =>
        natDegree_sum_le_of_forall_le _ _ fun l _ => ?_
    by_cases h : g = i + j + l
    · refine (natDegree_mul_le).trans ?_
      have h1 : (C (if g = i + j + l then c i j l else 0) * A ^ i).natDegree ≤ 2 * i :=
        (natDegree_C_mul_le _ _).trans ((natDegree_pow_le).trans (by nlinarith))
      have h2 : ((X : ℚ[X]) ^ j).natDegree ≤ j := natDegree_pow_le.trans (by
        nlinarith [natDegree_X_le (R := ℚ)])
      omega
    · simp [h]
  · rw [hET, finsetSum_coeff]
    simp only [R, eval_finsetSum, finsetSum_coeff, coeff_C_mul_X_pow, eval_mul, eval_C,
      eval_pow, eval_X, hAeval]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun l _ => ?_
    split_ifs <;> ring

end Langlands.Algebra.SeparatelyPolynomial
