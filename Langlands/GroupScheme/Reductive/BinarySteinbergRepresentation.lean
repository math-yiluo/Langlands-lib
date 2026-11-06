import Langlands.GroupScheme.Reductive.BinaryPolynomialMatrices
import Langlands.GroupScheme.Reductive.RankOnePolynomialActions

/-! # Actual binary polynomial representations at Steinberg degrees -/

noncomputable section

universe u

namespace Langlands.GroupScheme.HomogeneousPolynomial

open Matrix RankOneSteinberg

variable {R : Type u} [CommRing R]

/-- The actual special-linear action in the binary monomial coordinate space. -/
def binaryRepresentation (m : ℕ) :
    Representation R (Matrix.SpecialLinearGroup (Fin 2) R) (Fin (m + 1) → R) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp (binaryMatrixRepresentation m)

@[simp]
theorem binaryRepresentation_apply (m : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin 2) R) (x : Fin (m + 1) → R) :
    binaryRepresentation m g x = binaryMatrixRepresentation m g *ᵥ x :=
  rfl

section Field

variable {k : Type u} [Field k]

/-- A shifted binomial identity at a Steinberg degree. -/
theorem choose_steinberg_shift (p : ℕ) [Fact p.Prime] [CharP k p]
    (s c a : ℕ) (hca : c + a ≤ p ^ s - 1) :
    ((p ^ s - 1 - c).choose a : k) = (-1) ^ a * ((c + a).choose a : k) := by
  have h := congrArg (fun n : ℕ => (n : k))
    (Nat.choose_mul (n := p ^ s - 1) (k := c + a) (s := c) (by omega))
  push_cast at h
  rw [Nat.add_sub_cancel_left, Nat.choose_symm_add,
    choose_steinberg_cast p s (c + a) hca,
    choose_steinberg_cast p s c (by omega)] at h
  apply mul_left_cancel₀ (pow_ne_zero c (neg_ne_zero.mpr (one_ne_zero : (1 : k) ≠ 0)))
  simpa only [pow_add, mul_assoc] using h.symm

private theorem upperMatrix_apply (m : ℕ) (t : k) (r c : Fin (m + 1)) :
    upperMatrix k m t r c =
      if c.val ≤ r.val then (r.val.choose (r.val - c.val) : k) * t ^ (r.val - c.val)
      else 0 := by
  classical
  simp only [upperMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [raising, SplitExistence.gamE, Matrix.map_apply, Matrix.of_apply,
    apply_ite, map_natCast, map_zero, mul_zero]
  by_cases hcr : c.val ≤ r.val
  · rw [ite_eq_left hcr]
    let a : Fin (m + 1) := ⟨r.val - c.val, by have := r.isLt; omega⟩
    rw [Finset.sum_eq_single a]
    · simp [a, Nat.add_sub_of_le hcr, mul_comm]
    · intro b hb hba
      have hne : c.val + b.val ≠ r.val := by
        intro h
        apply hba
        apply Fin.ext
        dsimp [a]
        omega
      simp [hne]
    · simp
  · rw [ite_eq_right hcr]
    apply Finset.sum_eq_zero
    intro a ha
    have hne : c.val + a.val ≠ r.val := by omega
    simp [hne]

private theorem lowerMatrix_apply (m : ℕ) (t : k) (r c : Fin (m + 1)) :
    lowerMatrix k m t r c =
      if r.val ≤ c.val then ((m - r.val).choose (c.val - r.val) : k) * t ^ (c.val - r.val)
      else 0 := by
  classical
  simp only [lowerMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [lowering, SplitExistence.gamF, Matrix.map_apply, Matrix.of_apply,
    apply_ite, map_natCast, map_zero, mul_zero]
  by_cases hrc : r.val ≤ c.val
  · rw [ite_eq_left hrc]
    let a : Fin (m + 1) := ⟨c.val - r.val, by have := c.isLt; omega⟩
    rw [Finset.sum_eq_single a]
    · simp [a, Nat.add_sub_of_le hrc, mul_comm]
    · intro b hb hba
      have hne : r.val + b.val ≠ c.val := by
        intro h
        apply hba
        apply Fin.ext
        dsimp [a]
        omega
      simp [hne]
    · simp
  · rw [ite_eq_right hrc]
    apply Finset.sum_eq_zero
    intro a ha
    have hne : r.val + a.val ≠ c.val := by omega
    simp [hne]

/-- At a Steinberg degree the actual upper transvection gives the divided-power
polynomial family with negated parameter. -/
theorem binaryMatrixRepresentation_upper_steinberg (p : ℕ) [Fact p.Prime] [CharP k p]
    (s : ℕ) (t : k) :
    binaryMatrixRepresentation (p ^ s - 1) (upperRoot t) =
      upperMatrix k (p ^ s - 1) (-t) := by
  ext r c
  rw [binaryMatrixRepresentation_upper, upperMatrix_apply]
  by_cases hcr : c.val ≤ r.val
  · rw [ite_eq_left hcr, ite_eq_left hcr]
    have hr : c.val + (r.val - c.val) = r.val := Nat.add_sub_of_le hcr
    rw [choose_steinberg_shift p s c.val (r.val - c.val) (by have := r.isLt; omega), hr]
    rw [show -t = (-1 : k) * t by ring, mul_pow]
    ring
  · rw [ite_eq_right hcr, ite_eq_right hcr]

/-- At a Steinberg degree the actual lower transvection gives the divided-power
polynomial family with negated parameter. -/
theorem binaryMatrixRepresentation_lower_steinberg (p : ℕ) [Fact p.Prime] [CharP k p]
    (s : ℕ) (t : k) :
    binaryMatrixRepresentation (p ^ s - 1) (lowerRoot t) =
      lowerMatrix k (p ^ s - 1) (-t) := by
  ext r c
  rw [binaryMatrixRepresentation_lower, lowerMatrix_apply]
  by_cases hrc : r.val ≤ c.val
  · rw [ite_eq_left hrc, ite_eq_left hrc]
    have hc : r.val + (c.val - r.val) = c.val := Nat.add_sub_of_le hrc
    have h := choose_steinberg_shift (k := k) p s r.val (c.val - r.val)
      (by have := c.isLt; omega)
    rw [hc] at h
    rw [h, show -t = (-1 : k) * t by ring, mul_pow]
    have he : ((-1 : k) ^ (c.val - r.val)) * (-1) ^ (c.val - r.val) = 1 := by
      rw [← mul_pow]
      simp
    symm
    calc
      _ = (((-1 : k) ^ (c.val - r.val)) * (-1) ^ (c.val - r.val)) *
          ((c.val.choose (c.val - r.val) : k) * t ^ (c.val - r.val)) := by ring
      _ = _ := by rw [he, one_mul]
  · rw [ite_eq_right hrc, ite_eq_right hrc]

/-- The concrete root realization for the actual binary polynomial representation. -/
def binaryPolynomialRootRealization (p : ℕ) [Fact p.Prime] [CharP k p] [Infinite k]
    (s : ℕ) : PolynomialRootRealization p s (binaryRepresentation (R := k) (p ^ s - 1)) where
  upperPoint t := upperRoot (-t)
  lowerPoint t := lowerRoot (-t)
  upper_action t x := by
    rw [binaryRepresentation_apply, binaryMatrixRepresentation_upper_steinberg p s, neg_neg]
  lower_action t x := by
    rw [binaryRepresentation_apply, binaryMatrixRepresentation_lower_steinberg p s, neg_neg]

/-- The actual SL(2,k) binary polynomial representation is irreducible at every
Steinberg degree over an infinite field of characteristic p. -/
theorem binaryRepresentation_isIrreducible (p : ℕ) [Fact p.Prime] [CharP k p] [Infinite k]
    (s : ℕ) : (binaryRepresentation (R := k) (p ^ s - 1)).IsIrreducible :=
  irreducible_of_polynomialRootRealization p s _ (binaryPolynomialRootRealization p s)

end Field

end Langlands.GroupScheme.HomogeneousPolynomial
