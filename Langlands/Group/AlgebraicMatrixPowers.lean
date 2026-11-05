import Langlands.Group.PositivePowerPolynomial
import Langlands.GroupScheme.GeneralLinear
import Mathlib.Algebra.MvPolynomial.Monad

/-! # Positive diagonal powers inside polynomially defined matrix subgroups -/

noncomputable section

universe u

namespace Langlands.Group.AlgebraicMatrixPowers

open Matrix
open Langlands.GroupScheme.GeneralLinear
open Langlands.Group.PositivePowerPolynomial
open scoped BigOperators

variable {𝕜 : Type u} [RCLike 𝕜] {n : Type} [Fintype n] [DecidableEq n]

/-- The diagonal unit with entries the real powers of positive real numbers. -/
def diagonalPower (x : n → ℝ) (hx : ∀ i, 0 < x i) (r : ℝ) : GL n 𝕜 where
  val := diagonal (powerPoint x r)
  inv := diagonal (fun i => (powerPoint x r i : 𝕜)⁻¹)
  val_inv := by
    simp only [diagonal_mul_diagonal, diagonal_eq_one, funext_iff, Pi.one_apply]
    intro i
    exact mul_inv_cancel₀
      (RCLike.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (hx i) r).ne')
  inv_val := by
    simp only [diagonal_mul_diagonal, diagonal_eq_one, funext_iff, Pi.one_apply]
    intro i
    exact inv_mul_cancel₀
      (RCLike.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (hx i) r).ne')

@[simp] theorem diagonalPower_val (x : n → ℝ) (hx : ∀ i, 0 < x i) (r : ℝ) :
    (diagonalPower (𝕜 := 𝕜) x hx r).val = diagonal (powerPoint x r) := rfl

@[simp] theorem diagonalPower_inv_val (x : n → ℝ) (hx : ∀ i, 0 < x i) (r : ℝ) :
    ((diagonalPower (𝕜 := 𝕜) x hx r)⁻¹).val =
      diagonal (fun i => (powerPoint x r i : 𝕜)⁻¹) := rfl

theorem diagonalPower_natCast (x : n → ℝ) (hx : ∀ i, 0 < x i) (m : ℕ) :
    (diagonalPower x hx (m : ℝ) : GL n 𝕜) = diagonalPower x hx 1 ^ m := by
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, diagonalPower_val, diagonal_pow]
  congr 1
  funext i
  change (powerPoint x (m : ℝ) i : 𝕜) = powerPoint x 1 i ^ m
  simp only [powerPoint, Real.rpow_natCast, Real.rpow_one, RCLike.ofReal_pow]

/-- A conjugated positive diagonal one-parameter family of matrix units. -/
def conjugatedPower (U : GL n 𝕜) (x : n → ℝ) (hx : ∀ i, 0 < x i)
    (r : ℝ) : GL n 𝕜 :=
  (MulAut.conj U) (diagonalPower x hx r)

theorem conjugatedPower_natCast (U : GL n 𝕜) (x : n → ℝ) (hx : ∀ i, 0 < x i)
    (m : ℕ) :
    conjugatedPower U x hx (m : ℝ) = conjugatedPower U x hx 1 ^ m := by
  simp only [conjugatedPower, diagonalPower_natCast, map_pow]

/-- Both the diagonal eigenvalues and the inverse diagonal eigenvalues. -/
def doubledValues (x : n → ℝ) : n ⊕ n → ℝ :=
  Sum.elim x (fun i => (x i)⁻¹)

omit [Fintype n] [DecidableEq n] in
private theorem doubledValues_pos (x : n → ℝ) (hx : ∀ i, 0 < x i) :
    ∀ i, 0 < doubledValues x i := by
  intro i
  cases i with
  | inl i => exact hx i
  | inr i => exact inv_pos.mpr (hx i)

/-- Polynomial coordinates of a conjugated diagonal matrix and its inverse. -/
def conjugatedCoordinate (U : GL n 𝕜) :
    Coordinate n → MvPolynomial (n ⊕ n) 𝕜
  | .entry i j =>
      ∑ k, MvPolynomial.C (U i k * U⁻¹ k j) * MvPolynomial.X (Sum.inl k)
  | .inverseEntry i j =>
      ∑ k, MvPolynomial.C (U i k * U⁻¹ k j) * MvPolynomial.X (Sum.inr k)

private theorem eval_conjugatedCoordinate (U : GL n 𝕜) (x : n → ℝ)
    (hx : ∀ i, 0 < x i) (r : ℝ) (κ : Coordinate n) :
    MvPolynomial.eval (powerPoint (doubledValues x) r) (conjugatedCoordinate U κ) =
      values (conjugatedPower U x hx r) κ := by
  cases κ with
  | entry i j =>
    change MvPolynomial.eval _ (∑ k, MvPolynomial.C (U i k * U⁻¹ k j) *
      MvPolynomial.X (Sum.inl k)) = _
    simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    change (∑ k, (U i k * U⁻¹ k j) * (powerPoint x r k : 𝕜)) =
      (U.val * diagonal (powerPoint (𝕜 := 𝕜) x r) * (U⁻¹).val) i j
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_diagonal]; ring
  | inverseEntry i j =>
    change MvPolynomial.eval _ (∑ k, MvPolynomial.C (U i k * U⁻¹ k j) *
      MvPolynomial.X (Sum.inr k)) = _
    simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    change (∑ k, (U i k * U⁻¹ k j) *
      RCLike.ofReal ((x k)⁻¹ ^ r)) =
        (((conjugatedPower U x hx r)⁻¹ : GL n 𝕜) : Matrix n n 𝕜) i j
    have hp (k : n) :
        (RCLike.ofReal ((x k)⁻¹ ^ r) : 𝕜) = (powerPoint x r k)⁻¹ := by
      rw [← Real.rpow_neg_eq_inv_rpow, Real.rpow_neg (hx k).le, RCLike.ofReal_inv]
      rfl
    simp only [hp]
    change (∑ k, (U i k * U⁻¹ k j) * (powerPoint x r k : 𝕜)⁻¹) =
      (((MulAut.conj U) (diagonalPower x hx r))⁻¹).val i j
    rw [← map_inv, MulAut.conj_apply]
    change _ = (U.val *
      diagonal (fun k => (powerPoint x r k : 𝕜)⁻¹) *
      (U⁻¹).val) i j
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_diagonal]; ring

private theorem eval_bind_conjugatedCoordinate
    (U : GL n 𝕜) (x : n → ℝ) (hx : ∀ i, 0 < x i) (r : ℝ)
    (p : MvPolynomial (Coordinate n) 𝕜) :
    MvPolynomial.eval (powerPoint (doubledValues x) r)
        (MvPolynomial.bind₁ (conjugatedCoordinate U) p) =
      MvPolynomial.eval (values (conjugatedPower U x hx r)) p := by
  change MvPolynomial.eval₂Hom (RingHom.id _) _
    (MvPolynomial.bind₁ (conjugatedCoordinate U) p) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  change MvPolynomial.eval
    (fun κ => MvPolynomial.eval (powerPoint (doubledValues x) r)
      (conjugatedCoordinate U κ)) p = _
  have he : (fun κ => MvPolynomial.eval (powerPoint (doubledValues x) r)
      (conjugatedCoordinate U κ)) = values (conjugatedPower U x hx r) :=
    funext (eval_conjugatedCoordinate U x hx r)
  rw [he]

/-- Membership is cut out by polynomials in the matrix and inverse entries. -/
def IsPolynomiallyDefined (H : Subgroup (GL n 𝕜)) : Prop :=
  ∃ S : Set (MvPolynomial (Coordinate n) 𝕜), ∀ g : GL n 𝕜,
    g ∈ H ↔ ∀ p ∈ S, MvPolynomial.eval (values g) p = 0

/-- A polynomially defined matrix subgroup containing one positive diagonal
conjugate contains all its real powers in that same diagonalization. -/
theorem conjugatedPower_mem
    (H : Subgroup (GL n 𝕜)) (hH : IsPolynomiallyDefined H)
    (U : GL n 𝕜) (x : n → ℝ) (hx : ∀ i, 0 < x i)
    (h : conjugatedPower U x hx 1 ∈ H) (r : ℝ) :
    conjugatedPower U x hx r ∈ H := by
  obtain ⟨S, hS⟩ := hH
  apply (hS _).mpr
  intro p hp
  rw [← eval_bind_conjugatedCoordinate U x hx r p]
  apply eval_powerPoint_eq_zero _
    (doubledValues x) (fun i => (doubledValues_pos x hx i).le)
  intro m
  rw [eval_bind_conjugatedCoordinate, conjugatedPower_natCast]
  exact (hS _).mp (H.pow_mem h m) p hp

end Langlands.Group.AlgebraicMatrixPowers
