import Langlands.Representation.RankinSelberg.CharacterChange

/-!
# Block geometry for unequal-rank additive-character transport
-/

noncomputable section

namespace Langlands.RankinSelberg

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis

universe uF

variable {F : Type uF} [Field F]

/-- The fixed right correction has the scalar block `a^d I_(n+1)` followed
by the trailing entries of the large character-change diagonal. -/
def characterChangeBlockCorrection (a : Fˣ) (n d : ℕ) :
    Langlands.GeneralLinear (n + d + 1) F where
  val := Matrix.diagonal fun i =>
    ((a ^ (if i.val < n + 1 then d else n + d - i.val) : Fˣ) : F)
  inv := Matrix.diagonal fun i =>
    (((a ^ (if i.val < n + 1 then d else n + d - i.val))⁻¹ : Fˣ) : F)
  val_inv := by simp [Matrix.diagonal_mul_diagonal]
  inv_val := by simp [Matrix.diagonal_mul_diagonal]

/-- Scale rectangular row `i` by `a^(-(i+1))`. -/
def characterChangeRectangular (a : Fˣ) (j n : ℕ) :
    Matrix (Fin j) (Fin (n + 1)) F ≃ₗ[F] Matrix (Fin j) (Fin (n + 1)) F where
  toFun x i l := (((a ^ (i.val + 1))⁻¹ : Fˣ) : F) * x i l
  invFun x i l := ((a ^ (i.val + 1) : Fˣ) : F) * x i l
  left_inv x := by ext i l; simp
  right_inv x := by ext i l; simp
  map_add' x y := by ext i l; exact mul_add _ _ _
  map_smul' c x := by ext i l; exact mul_left_comm _ _ _

@[simp] theorem characterChangeRectangular_apply (a : Fˣ) (j n : ℕ)
    (x : Matrix (Fin j) (Fin (n + 1)) F) (i : Fin j) (l : Fin (n + 1)) :
    characterChangeRectangular a j n x i l =
      (((a ^ (i.val + 1))⁻¹ : Fˣ) : F) * x i l := rfl

@[simp] theorem characterChangeRectangular_symm_apply (a : Fˣ) (j n : ℕ)
    (x : Matrix (Fin j) (Fin (n + 1)) F) (i : Fin j) (l : Fin (n + 1)) :
    (characterChangeRectangular a j n).symm x i l =
      ((a ^ (i.val + 1) : Fˣ) : F) * x i l := rfl

private theorem diagonal_row_scale (a : Fˣ) (d r : ℕ) (h : r ≤ d) :
    ((a ^ (d - r) : Fˣ) : F) = (((a ^ r)⁻¹ : Fˣ) : F) * ((a ^ d : Fˣ) : F) := by
  have hd : d = r + (d - r) := by omega
  conv_rhs => rw [hd, pow_add]
  simp only [← Units.val_mul, inv_mul_cancel_left]

/-- Exact matrix identity behind the unequal-rank change of variables. -/
theorem unequalRankMatrix_characterChange (a : Fˣ) (n j k : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F)
    (x : Matrix (Fin j) (Fin (n + 1)) F) :
    characterChangeElement a (n + (j + k + 1)) * unequalRankMatrix j k g x =
      unequalRankMatrix j k (characterChangeElement a n * g)
        (characterChangeRectangular a j n x) *
          characterChangeBlockCorrection a n (j + k + 1) := by
  apply Units.ext
  ext i l
  simp only [Units.val_mul, characterChangeElement_val, unequalRankMatrix_val,
    characterChangeBlockCorrection, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.add_apply]
  by_cases hi : i.val < n + 1
  · have hir : ¬ (n + 1 ≤ i.val ∧ i.val < n + 1 + j) := by omega
    by_cases hl : l.val < n + 1
    · simp only [appendIdentity_entry, dite_eq_left hi, dite_eq_left hl, rectangularEntries,
        dite_eq_right hir, add_zero, ite_eq_left hl]
      change ((a ^ (n + (j + k + 1) - i.val) : Fˣ) : F) * g _ _ =
        (characterChangeElement a n * g).val _ _ * ((a ^ (j + k + 1) : Fˣ) : F)
      rw [show n + (j + k + 1) - i.val = (n - i.val) + (j + k + 1) by omega,
        pow_add, Units.val_mul]
      simp only [Units.val_mul, characterChangeElement_val, Matrix.diagonal_mul]
      ring
    · simp only [appendIdentity_entry, dite_eq_left hi, dite_eq_right hl, rectangularEntries,
        dite_eq_right hir, add_zero, mul_zero, zero_mul]
  · by_cases hl : l.val < n + 1
    · have hil : i ≠ l := by intro h; subst l; contradiction
      by_cases hir : n + 1 ≤ i.val ∧ i.val < n + 1 + j
      · simp only [appendIdentity_entry, dite_eq_right hi, ite_eq_right hil, zero_add,
          rectangularEntries, dite_eq_left hir, dite_eq_left hl, ite_eq_left hl,
          characterChangeRectangular_apply]
        have he : n + (j + k + 1) - i.val =
            (j + k + 1) - (i.val - (n + 1) + 1) := by omega
        rw [he, diagonal_row_scale a (j + k + 1) (i.val - (n + 1) + 1) (by omega)]
        ring
      · simp only [appendIdentity_entry, dite_eq_right hi, ite_eq_right hil, rectangularEntries,
          dite_eq_right hir, add_zero, mul_zero, zero_mul]
    · by_cases hil : i = l
      · subst l
        simp only [appendIdentity_entry, dite_eq_right hi, rectangularEntries, ite_eq_right hi]
        exact mul_comm _ _
      · simp only [appendIdentity_entry, dite_eq_right hi, ite_eq_right hil, rectangularEntries,
          dite_eq_right hl]
        split <;> simp

end Langlands.RankinSelberg
