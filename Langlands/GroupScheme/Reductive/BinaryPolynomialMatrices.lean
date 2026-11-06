import Langlands.GroupScheme.Reductive.BinaryPolynomialRootActions
import Langlands.GroupScheme.Reductive.BinaryHomogeneousBasis
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Matrices of the binary homogeneous polynomial representation -/

noncomputable section

universe u

namespace Langlands.GroupScheme.HomogeneousPolynomial

open MvPolynomial Matrix

variable {R : Type u} [CommRing R]

/-- The actual special-linear representation in the binary monomial coordinates. -/
def binaryMatrixRepresentation (m : ℕ) :
    Matrix.SpecialLinearGroup (Fin 2) R →*
      Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  (LinearMap.toMatrixAlgEquiv (binaryBasis m)).toMonoidHom.comp
    (specialLinearRepresentation m)

theorem binaryMatrixRepresentation_apply (m : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin 2) R) (r c : Fin (m + 1)) :
    binaryMatrixRepresentation m g r c =
      (substitution (g : Matrix (Fin 2) (Fin 2) R)
        (binaryBasis (R := R) m c : MvPolynomial (Fin 2) R)).coeff (binaryExponent m r) := by
  change LinearMap.toMatrixAlgEquiv (binaryBasis m)
    (specialLinearRepresentation m g) r c = _
  rw [LinearMap.toMatrixAlgEquiv_apply, binaryBasis_repr_apply]
  rfl

private theorem binary_monomial_coeff (a b m : ℕ) (r : Fin (m + 1)) :
    (X 0 ^ a * X 1 ^ b : MvPolynomial (Fin 2) R).coeff (binaryExponent m r) =
      if a = r.val ∧ b = m - r.val then 1 else 0 := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, one_mul,
    coeff_monomial]
  have h :
      Finsupp.single (0 : Fin 2) a + Finsupp.single 1 b = binaryExponent m r ↔
        a = r.val ∧ b = m - r.val := by
    constructor
    · intro h
      exact ⟨by simpa using congrArg (fun d => d 0) h,
        by simpa using congrArg (fun d => d 1) h⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  simp only [h]

/-- The upper root matrix in the actual monomial basis. -/
theorem binaryMatrixRepresentation_upper (m : ℕ) (t : R) (r c : Fin (m + 1)) :
    binaryMatrixRepresentation m (upperRoot t) r c =
      if c.val ≤ r.val then
        ((m - c.val).choose (r.val - c.val) : R) * t ^ (r.val - c.val)
      else 0 := by
  classical
  rw [binaryMatrixRepresentation_apply, binaryBasis_apply, upperRoot_monomial, coeff_sum]
  simp only [coeff_C_mul, binary_monomial_coeff, mul_ite, mul_one, mul_zero]
  by_cases hcr : c.val ≤ r.val
  · rw [if_pos hcr]
    rw [Finset.sum_eq_single (r.val - c.val)]
    · simp [Nat.add_sub_of_le hcr, Nat.sub_sub]
    · intro a ha hne
      have hn : c.val + a ≠ r.val := by omega
      simp [hn]
    · intro hn
      exfalso
      apply hn
      rw [Finset.mem_range]
      have := r.isLt
      omega
  · rw [if_neg hcr]
    apply Finset.sum_eq_zero
    intro a ha
    have hn : c.val + a ≠ r.val := by omega
    simp [hn]

/-- The lower root matrix in the actual monomial basis. -/
theorem binaryMatrixRepresentation_lower (m : ℕ) (t : R) (r c : Fin (m + 1)) :
    binaryMatrixRepresentation m (lowerRoot t) r c =
      if r.val ≤ c.val then
        (c.val.choose (c.val - r.val) : R) * t ^ (c.val - r.val)
      else 0 := by
  classical
  rw [binaryMatrixRepresentation_apply, binaryBasis_apply, lowerRoot_monomial, coeff_sum]
  simp only [coeff_C_mul, binary_monomial_coeff, mul_ite, mul_one, mul_zero]
  by_cases hrc : r.val ≤ c.val
  · rw [if_pos hrc]
    rw [Finset.sum_eq_single (c.val - r.val)]
    · have hc : c.val ≤ m := Nat.le_of_lt_succ c.isLt
      have hfirst : c.val - (c.val - r.val) = r.val := by omega
      have hsecond : m - c.val + (c.val - r.val) = m - r.val := by omega
      simp [hfirst, hsecond]
    · intro a ha hne
      have ha' : a ≤ c.val := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
      have hn : c.val - a ≠ r.val := by omega
      simp [hn]
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr (by omega)))
  · rw [if_neg hrc]
    apply Finset.sum_eq_zero
    intro a ha
    have hn : c.val - a ≠ r.val := by omega
    simp [hn]

end Langlands.GroupScheme.HomogeneousPolynomial
