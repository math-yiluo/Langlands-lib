import Langlands.GroupScheme.Examples.SU3RootReflection
import Langlands.GroupScheme.Examples.SU3RootValuation

/-! # The sharp central depth of an opposite SU3 commutator -/

noncomputable section

namespace Langlands.GroupScheme.SU3Root

universe u

section Ring

variable {A : Type u} [CommRing A] {c : RingInvolution A}

/-- The commutator in the convention of KP Definition 7.1.3. -/
def oppositeCommutator (p q : Parameters c) :
    Matrix.GeneralLinearGroup (Fin 3) A :=
  (oppositeEmbedding c q)⁻¹ * Parameters.embedding c p *
    oppositeEmbedding c q * (Parameters.embedding c p)⁻¹

/-- The upper-left entry determines the central diagonal factor. -/
theorem oppositeCommutator_entry_zero_zero (p q : Parameters c) :
    oppositeCommutator p q 0 0 =
      1 - p.first * c.bar q.first + p.second * q.second := by
  unfold oppositeCommutator
  rw [← (oppositeEmbedding c).map_inv, ← (Parameters.embedding c).map_inv]
  change ((oppositeEmbedding c q⁻¹ : Matrix (Fin 3) (Fin 3) A) *
    Parameters.matrix p * (oppositeEmbedding c q : Matrix (Fin 3) (Fin 3) A) *
    Parameters.matrix p⁻¹) 0 0 = _
  rw [oppositeEmbedding_val, oppositeEmbedding_val]
  simp [Parameters.matrix, Matrix.mul_apply, Fin.sum_univ_three]
  ring

/-- In any opposite-root/diagonal/root factorization the diagonal parameter is
the upper-left entry. No existence of a factorization is assumed implicitly. -/
theorem diagonal_parameter_of_oppositeCommutator
    (p q v' v : Parameters c) (t : Aˣ)
    (h : oppositeCommutator p q =
      oppositeEmbedding c v' * diagonal c t * Parameters.embedding c v) :
    (t : A) = 1 - p.first * c.bar q.first + p.second * q.second := by
  have he := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 3) A => g 0 0) h
  rw [oppositeCommutator_entry_zero_zero] at he
  change _ = ((oppositeEmbedding c v' : Matrix (Fin 3) (Fin 3) A) *
    (diagonal c t : Matrix (Fin 3) (Fin 3) A) * Parameters.matrix v) 0 0 at he
  rw [oppositeEmbedding_val, diagonal_val] at he
  simpa [Parameters.matrix, Matrix.mul_apply, Fin.sum_univ_three] using he.symm

/-- When either root parameter belongs to the double-root subgroup, the
deviation of the central parameter is the product of the second coordinates. -/
theorem diagonal_sub_one_of_double_oppositeCommutator
    (p q v' v : Parameters c) (t : Aˣ)
    (hdouble : p.first = 0 ∨ q.first = 0)
    (h : oppositeCommutator p q =
      oppositeEmbedding c v' * diagonal c t * Parameters.embedding c v) :
    (t : A) - 1 = p.second * q.second := by
  rw [diagonal_parameter_of_oppositeCommutator p q v' v t h]
  rcases hdouble with hp | hq
  · simp [hp]
  · simp [hq]

end Ring

section Valuation

variable {L : Type u} [Field L] {c : RingInvolution L}
  (omega : AddValuation L (WithTop ℝ))

/-- The normalization of the multipliable-root depth doubles to the sum of
the second-coordinate valuations, including infinite depths. -/
theorem doubleTop_depthA_add_depthA (p q : Parameters c) :
    doubleTop (Parameters.depthA omega p + Parameters.depthA omega q) =
      omega p.second + omega q.second := by
  unfold Parameters.depthA
  cases omega p.second using WithTop.recTopCoe with
  | top => simp
  | coe s =>
    cases omega q.second using WithTop.recTopCoe with
    | top => simp
    | coe t =>
      simp only [halfTop_coe, ← WithTop.coe_add, doubleTop_coe, WithTop.coe_inj]
      ring

/-- The central parameter has exactly twice the sum of the two root depths
for a commutator involving a double-root element. -/
theorem value_diagonal_sub_one_of_double_oppositeCommutator
    (p q v' v : Parameters c) (t : Lˣ)
    (hdouble : p.first = 0 ∨ q.first = 0)
    (h : oppositeCommutator p q =
      oppositeEmbedding c v' * diagonal c t * Parameters.embedding c v) :
    omega ((t : L) - 1) =
      doubleTop (Parameters.depthA omega p + Parameters.depthA omega q) := by
  rw [diagonal_sub_one_of_double_oppositeCommutator p q v' v t hdouble h,
    omega.map_mul, doubleTop_depthA_add_depthA]

/-- Finite depth form of the sharp estimate used for the centralizer
filtration. The depth sum may have either sign. -/
theorem value_diagonal_sub_one_eq_double_of_depth_sum
    (p q v' v : Parameters c) (t : Lˣ)
    (hdouble : p.first = 0 ∨ q.first = 0)
    (h : oppositeCommutator p q =
      oppositeEmbedding c v' * diagonal c t * Parameters.embedding c v)
    (r : ℝ) (hr : Parameters.depthA omega p + Parameters.depthA omega q =
      (r : WithTop ℝ)) :
    omega ((t : L) - 1) = (↑(2 * r) : WithTop ℝ) := by
  rw [value_diagonal_sub_one_of_double_oppositeCommutator omega p q v' v t hdouble h,
    hr, doubleTop_coe]

end Valuation

end Langlands.GroupScheme.SU3Root
