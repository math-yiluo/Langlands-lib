import Langlands.LinearAlgebra.HomogeneousPolynomialMatrix

/-! # The common exponent in homogeneous polynomial determinant weights -/

noncomputable section

universe u w

namespace Langlands.LinearAlgebra.HomogeneousPolynomial

open MvPolynomial

variable {σ : Type w} {d : ℕ}

/-- Reindexing variables permutes the monomials of every fixed total degree. -/
def reindexMonomial (e : σ ≃ σ) (d : ℕ) : MonomialIndex σ d ≃ MonomialIndex σ d :=
  (Finsupp.domCongr e).toEquiv.subtypeEquiv (fun a => by
    change a.degree = d ↔ (Finsupp.equivMapDomain e a).degree = d
    simp only [Finsupp.equivMapDomain_eq_mapDomain, Finsupp.degree_mapDomain])

@[simp]
theorem reindexMonomial_apply (e : σ ≃ σ) (p : MonomialIndex σ d) (i : σ) :
    (reindexMonomial e d p).val i = p.val (e.symm i) := rfl

variable (σ) [Finite σ]

/-- The total exponent of one variable in all monomials of degree `d`. -/
def coordinateExponent (d : ℕ) (i : σ) : ℕ :=
  ∑ e : MonomialIndex σ d, e.val i

variable {σ}

/-- Symmetry of the monomial set makes the total exponent independent of the variable. -/
theorem coordinateExponent_eq (d : ℕ) (i j : σ) :
    coordinateExponent σ d i = coordinateExponent σ d j := by
  classical
  apply Fintype.sum_equiv (reindexMonomial (Equiv.swap i j) d)
  intro e
  simp only [reindexMonomial_apply, Equiv.symm_swap, Equiv.swap_apply_right]

theorem coordinateExponent_pos (d : ℕ) (hd : 0 < d) (i : σ) :
    0 < coordinateExponent σ d i := by
  classical
  let e : MonomialIndex σ d := ⟨Finsupp.single i d, by simp⟩
  have hle := Finset.single_le_sum
    (fun (p : MonomialIndex σ d) (_ : p ∈ Finset.univ) => Nat.zero_le (p.val i))
    (Finset.mem_univ e)
  have hle' : d ≤ coordinateExponent σ d i := by
    simpa [coordinateExponent, e] using hle
  exact lt_of_lt_of_le hd hle'

variable (σ)

/-- The homogeneous determinant exponent. The empty-variable convention is `d`;
all source matrices then have determinant one. -/
def exponent (d : ℕ) : ℕ := by
  classical
  exact if h : Nonempty σ then coordinateExponent σ d (Classical.choice h) else d

theorem exponent_eq_coordinate (d : ℕ) (i : σ) :
    exponent σ d = coordinateExponent σ d i := by
  classical
  rw [exponent, dite_eq_left ⟨i⟩]
  exact coordinateExponent_eq d _ i

theorem exponent_pos (d : ℕ) (hd : 0 < d) : 0 < exponent σ d := by
  classical
  by_cases h : Nonempty σ
  · rw [exponent, dite_eq_left h]
    exact coordinateExponent_pos d hd _
  · simpa only [exponent, dite_eq_right h] using hd

variable {σ}

section Diagonal

variable {R : Type u} [CommRing R] [Fintype σ] [DecidableEq σ]

/-- The diagonal homogeneous determinant is the product of the coordinate powers. -/
theorem det_representation_diagonal_coordinate (a : σ → R) (d : ℕ) :
    (representation (Matrix.diagonal a) d).det =
      ∏ i, a i ^ coordinateExponent σ d i := by
  rw [det_representation_diagonal]
  simp_rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  exact Finset.prod_pow_eq_pow_sum _ _ _

/-- For every diagonal matrix, homogeneous substitution has determinant equal to
the source determinant raised to the common natural exponent. -/
theorem det_representation_diagonal_pow (a : σ → R) (d : ℕ) :
    (representation (Matrix.diagonal a) d).det =
      (Matrix.diagonal a).det ^ exponent σ d := by
  classical
  rw [det_representation_diagonal_coordinate, Matrix.det_diagonal, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j _
  rw [exponent_eq_coordinate σ d j]

end Diagonal

end Langlands.LinearAlgebra.HomogeneousPolynomial
