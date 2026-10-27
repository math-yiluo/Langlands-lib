import Langlands.Group.GL.OneBlockShape
import Langlands.Group.GL.AdjacentMergeShape
import Langlands.Representation.Shahidi.TwoBlocks

/-! Ordered refinement data for the two bracketings of three consecutive blocks. -/

namespace Langlands.Parabolic

open GeneralLinear Geometric Shahidi

variable (C A B : ℕ) (hC : 0 < C) (hA : 0 < A) (hB : 0 < B)

/-- The ordered three-block shape `(C, A, B)` of total rank `C + (A + B)`. -/
abbrev threeBlocks : BlockShape (C + (A + B)) where
  length := 3
  size := ![C, A, B]
  positive := by
    intro i
    fin_cases i <;> assumption
  sum_eq := by
    simp only [Fin.sum_univ_three]
    exact Nat.add_assoc C A B

/-- The same ordered three-block shape `(C, A, B)`, of total rank `(C + A) + B`. -/
abbrev threeBlocksRight : BlockShape (C + A + B) where
  length := 3
  size := ![C, A, B]
  positive := by
    intro i
    fin_cases i <;> assumption
  sum_eq := by
    simp only [Fin.sum_univ_three]
    rfl

theorem threeBlocksRight_eq_rankCast :
    threeBlocksRight C A B hC hA hB =
      (threeBlocks C A B hC hA hB).rankCast (Nat.add_assoc C A B).symm := rfl

/-! ### The bracketing `C, (A, B)` -/

/-- Refine the outer shape `(C, A + B)` by one block `C` and the two blocks `(A, B)`. -/
def leftRefinement :
    BlockRefinement (twoBlocks C (A + B) hC (Nat.add_pos_left hA B)) :=
  Fin.cases (CuspidalSupport.LeviAdmissibility.oneBlock C hC) (Fin.cases (twoBlocks A B hA hB) finZeroElim)

/-- Nested labels of the left bracketing, numbered consecutively. -/
def leftLabel :
    ((j : Fin 2) × Fin (leftRefinement C A B hC hA hB j).length) → Fin 3
  | ⟨⟨0, _⟩, _⟩ => 0
  | ⟨⟨1, _⟩, k⟩ => k.succ

/-- The inverse numbering of the left bracketing. -/
def leftLabelInv :
    Fin 3 → ((j : Fin 2) × Fin (leftRefinement C A B hC hA hB j).length)
  | ⟨0, _⟩ => ⟨0, ⟨0, Nat.one_pos⟩⟩
  | ⟨1, _⟩ => ⟨1, ⟨0, Nat.two_pos⟩⟩
  | ⟨2, _⟩ => ⟨1, ⟨1, Nat.one_lt_two⟩⟩

/-- The consecutive numbering of nested labels of the left bracketing. -/
def leftLabelEquiv :
    ((j : Fin 2) × Fin (leftRefinement C A B hC hA hB j).length) ≃ Fin 3 where
  toFun := leftLabel C A B hC hA hB
  invFun := leftLabelInv C A B hC hA hB
  left_inv := by
    rintro ⟨j, k⟩
    fin_cases j <;> fin_cases k <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem leftLabelEquiv_size (a : (j : Fin 2) × Fin (leftRefinement C A B hC hA hB j).length) :
    (leftRefinement C A B hC hA hB a.1).size a.2 =
      (threeBlocks C A B hC hA hB).size (leftLabelEquiv C A B hC hA hB a) := by
  rcases a with ⟨j, k⟩
  fin_cases j <;> fin_cases k <;> rfl

theorem leftLabelEquiv_val (a : (j : Fin 2) × Fin (leftRefinement C A B hC hA hB j).length) :
    (leftLabelEquiv C A B hC hA hB a : ℕ) = a.1.val + a.2.val := by
  rcases a with ⟨j, k⟩
  fin_cases j <;> fin_cases k <;> rfl

theorem leftLabelEquiv_lex (a b : (j : Fin 2) × Fin (leftRefinement C A B hC hA hB j).length)
    (hab : a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2.val < b.2.val)) :
    leftLabelEquiv C A B hC hA hB a < leftLabelEquiv C A B hC hA hB b := by
  rw [Fin.lt_def, leftLabelEquiv_val, leftLabelEquiv_val]
  rcases a with ⟨j, k⟩
  rcases b with ⟨j', k'⟩
  fin_cases j <;> fin_cases k <;> fin_cases j' <;> fin_cases k' <;> simp_all

/-- The exact consecutive-coordinate identity of the left bracketing. -/
theorem leftLabelEquiv_index (j : Fin 2) (k : Fin (leftRefinement C A B hC hA hB j).length)
    (x : Fin ((leftRefinement C A B hC hA hB j).size k)) :
    (twoBlocks C (A + B) hC (Nat.add_pos_left hA B)).index j
        ((leftRefinement C A B hC hA hB j).index k x) =
      (threeBlocks C A B hC hA hB).index (leftLabelEquiv C A B hC hA hB ⟨j, k⟩)
        (Fin.cast (leftLabelEquiv_size C A B hC hA hB ⟨j, k⟩) x) :=
  BlockShape.index_index_eq_of_lex (threeBlocks C A B hC hA hB)
    (twoBlocks C (A + B) hC (Nat.add_pos_left hA B)) (leftRefinement C A B hC hA hB)
    (leftLabelEquiv C A B hC hA hB) (leftLabelEquiv_size C A B hC hA hB)
    (leftLabelEquiv_lex C A B hC hA hB) j k x

/-! ### The bracketing `(C, A), B` -/

/-- Refine the outer shape `(C + A, B)` by the two blocks `(C, A)` and one block `B`. -/
def rightRefinement :
    BlockRefinement (twoBlocks (C + A) B (Nat.add_pos_left hC A) hB) :=
  Fin.cases (twoBlocks C A hC hA) (Fin.cases (CuspidalSupport.LeviAdmissibility.oneBlock B hB) finZeroElim)

/-- Nested labels of the right bracketing, numbered consecutively. -/
def rightLabel :
    ((j : Fin 2) × Fin (rightRefinement C A B hC hA hB j).length) → Fin 3
  | ⟨⟨0, _⟩, k⟩ => k.castSucc
  | ⟨⟨1, _⟩, _⟩ => 2

/-- The inverse numbering of the right bracketing. -/
def rightLabelInv :
    Fin 3 → ((j : Fin 2) × Fin (rightRefinement C A B hC hA hB j).length)
  | ⟨0, _⟩ => ⟨0, ⟨0, Nat.two_pos⟩⟩
  | ⟨1, _⟩ => ⟨0, ⟨1, Nat.one_lt_two⟩⟩
  | ⟨2, _⟩ => ⟨1, ⟨0, Nat.one_pos⟩⟩

/-- The consecutive numbering of nested labels of the right bracketing. -/
def rightLabelEquiv :
    ((j : Fin 2) × Fin (rightRefinement C A B hC hA hB j).length) ≃ Fin 3 where
  toFun := rightLabel C A B hC hA hB
  invFun := rightLabelInv C A B hC hA hB
  left_inv := by
    rintro ⟨j, k⟩
    fin_cases j <;> fin_cases k <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

theorem rightLabelEquiv_size (a : (j : Fin 2) × Fin (rightRefinement C A B hC hA hB j).length) :
    (rightRefinement C A B hC hA hB a.1).size a.2 =
      (threeBlocksRight C A B hC hA hB).size (rightLabelEquiv C A B hC hA hB a) := by
  rcases a with ⟨j, k⟩
  fin_cases j <;> fin_cases k <;> rfl

theorem rightLabelEquiv_val (a : (j : Fin 2) × Fin (rightRefinement C A B hC hA hB j).length) :
    (rightLabelEquiv C A B hC hA hB a : ℕ) = 2 * a.1.val + a.2.val := by
  rcases a with ⟨j, k⟩
  fin_cases j <;> fin_cases k <;> rfl

theorem rightLabelEquiv_lex (a b : (j : Fin 2) × Fin (rightRefinement C A B hC hA hB j).length)
    (hab : a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2.val < b.2.val)) :
    rightLabelEquiv C A B hC hA hB a < rightLabelEquiv C A B hC hA hB b := by
  rw [Fin.lt_def, rightLabelEquiv_val, rightLabelEquiv_val]
  rcases a with ⟨j, k⟩
  rcases b with ⟨j', k'⟩
  fin_cases j <;> fin_cases k <;> fin_cases j' <;> fin_cases k' <;> simp_all

/-- The exact consecutive-coordinate identity of the right bracketing. -/
theorem rightLabelEquiv_index (j : Fin 2) (k : Fin (rightRefinement C A B hC hA hB j).length)
    (x : Fin ((rightRefinement C A B hC hA hB j).size k)) :
    (twoBlocks (C + A) B (Nat.add_pos_left hC A) hB).index j
        ((rightRefinement C A B hC hA hB j).index k x) =
      (threeBlocksRight C A B hC hA hB).index (rightLabelEquiv C A B hC hA hB ⟨j, k⟩)
        (Fin.cast (rightLabelEquiv_size C A B hC hA hB ⟨j, k⟩) x) :=
  BlockShape.index_index_eq_of_lex (threeBlocksRight C A B hC hA hB)
    (twoBlocks (C + A) B (Nat.add_pos_left hC A) hB) (rightRefinement C A B hC hA hB)
    (rightLabelEquiv C A B hC hA hB) (rightLabelEquiv_size C A B hC hA hB)
    (rightLabelEquiv_lex C A B hC hA hB) j k x

end Langlands.Parabolic
