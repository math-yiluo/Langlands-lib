import Langlands.Group.GL.SingleBlock
import Langlands.Group.GL.AdjacentMergeShape
import Langlands.Representation.Parabolic.ThreeBlockRefinementGeometry

/-!
# Literal two-grouping geometry for three positive blocks

Both bracketings of three consecutive blocks `(C, A, B)` as ordered refinement data at the
single total rank `C + (A + B)`. The bracketing `C, (A, B)` is the published data of
`ThreeBlockRefinementGeometry`; the bracketing `(C, A), B` is stated for the outer shape
`(twoBlocks (C + A) B).rankCast (Nat.add_assoc C A B)` against `threeBlocks` itself. The
module also records the specialization, length, size and label-value laws as named lemmas.
-/

namespace Langlands.Parabolic

open GeneralLinear Geometric Shahidi

variable (C A B : ℕ) (hC : 0 < C) (hA : 0 < A) (hB : 0 < B)

/-! ### The three-block shape -/

theorem threeBlocks_length : (threeBlocks C A B hC hA hB).length = 3 := rfl

theorem threeBlocks_size : (threeBlocks C A B hC hA hB).size = ![C, A, B] := rfl

/-! ### The bracketing `C, (A, B)` -/

theorem leftRefinement_zero :
    leftRefinement C A B hC hA hB 0 = CuspidalSupport.LeviAdmissibility.oneBlock C hC := rfl

theorem leftRefinement_one : leftRefinement C A B hC hA hB 1 = twoBlocks A B hA hB := rfl

theorem leftRefinement_length_zero : (leftRefinement C A B hC hA hB 0).length = 1 := rfl

theorem leftRefinement_length_one : (leftRefinement C A B hC hA hB 1).length = 2 := rfl

theorem leftRefinement_size_zero : (leftRefinement C A B hC hA hB 0).size = fun _ => C := rfl

theorem leftRefinement_size_one : (leftRefinement C A B hC hA hB 1).size = ![A, B] := rfl

theorem leftLabelEquiv_apply_zero_zero :
    leftLabelEquiv C A B hC hA hB ⟨0, ⟨0, Nat.one_pos⟩⟩ = 0 := rfl

theorem leftLabelEquiv_apply_one_zero :
    leftLabelEquiv C A B hC hA hB ⟨1, ⟨0, Nat.two_pos⟩⟩ = 1 := rfl

theorem leftLabelEquiv_apply_one_one :
    leftLabelEquiv C A B hC hA hB ⟨1, ⟨1, Nat.one_lt_two⟩⟩ = 2 := rfl

/-! ### The bracketing `(C, A), B` at total rank `C + (A + B)` -/

/-- Refine the outer shape `(C + A, B)`, cast to total rank `C + (A + B)`, by the two blocks
`(C, A)` and one block `B`. -/
def rankCastRightRefinement :
    BlockRefinement
      ((twoBlocks (C + A) B (Nat.add_pos_left hC A) hB).rankCast (Nat.add_assoc C A B)) :=
  rightRefinement C A B hC hA hB

theorem rankCastRightRefinement_zero :
    rankCastRightRefinement C A B hC hA hB (0 : Fin 2) = twoBlocks C A hC hA := rfl

theorem rankCastRightRefinement_one :
    rankCastRightRefinement C A B hC hA hB (1 : Fin 2) =
      CuspidalSupport.LeviAdmissibility.oneBlock B hB := rfl

theorem rankCastRightRefinement_length_zero :
    (rankCastRightRefinement C A B hC hA hB (0 : Fin 2)).length = 2 := rfl

theorem rankCastRightRefinement_length_one :
    (rankCastRightRefinement C A B hC hA hB (1 : Fin 2)).length = 1 := rfl

theorem rankCastRightRefinement_size_zero :
    (rankCastRightRefinement C A B hC hA hB (0 : Fin 2)).size = ![C, A] := rfl

theorem rankCastRightRefinement_size_one :
    (rankCastRightRefinement C A B hC hA hB (1 : Fin 2)).size = fun _ => B := rfl

/-- The consecutive numbering of nested labels of the cast right bracketing. -/
def rankCastRightLabelEquiv :
    ((j : Fin ((twoBlocks (C + A) B (Nat.add_pos_left hC A) hB).rankCast
        (Nat.add_assoc C A B)).length) ×
      Fin (rankCastRightRefinement C A B hC hA hB j).length) ≃ Fin 3 :=
  rightLabelEquiv C A B hC hA hB

theorem rankCastRightLabelEquiv_apply_zero_zero :
    rankCastRightLabelEquiv C A B hC hA hB ⟨(0 : Fin 2), ⟨0, Nat.two_pos⟩⟩ = 0 := rfl

theorem rankCastRightLabelEquiv_apply_zero_one :
    rankCastRightLabelEquiv C A B hC hA hB ⟨(0 : Fin 2), ⟨1, Nat.one_lt_two⟩⟩ = 1 := rfl

theorem rankCastRightLabelEquiv_apply_one_zero :
    rankCastRightLabelEquiv C A B hC hA hB ⟨(1 : Fin 2), ⟨0, Nat.one_pos⟩⟩ = 2 := rfl

theorem rankCastRightLabelEquiv_val
    (a : (j : Fin ((twoBlocks (C + A) B (Nat.add_pos_left hC A) hB).rankCast
        (Nat.add_assoc C A B)).length) ×
      Fin (rankCastRightRefinement C A B hC hA hB j).length) :
    (rankCastRightLabelEquiv C A B hC hA hB a : ℕ) = 2 * a.1.val + a.2.val :=
  rightLabelEquiv_val C A B hC hA hB a

theorem rankCastRightLabelEquiv_size
    (a : (j : Fin ((twoBlocks (C + A) B (Nat.add_pos_left hC A) hB).rankCast
        (Nat.add_assoc C A B)).length) ×
      Fin (rankCastRightRefinement C A B hC hA hB j).length) :
    (rankCastRightRefinement C A B hC hA hB a.1).size a.2 =
      (threeBlocks C A B hC hA hB).size (rankCastRightLabelEquiv C A B hC hA hB a) :=
  rightLabelEquiv_size C A B hC hA hB a

/-- The exact consecutive-coordinate identity of the cast right bracketing. -/
theorem rankCastRightLabelEquiv_index
    (j : Fin ((twoBlocks (C + A) B (Nat.add_pos_left hC A) hB).rankCast
      (Nat.add_assoc C A B)).length)
    (k : Fin (rankCastRightRefinement C A B hC hA hB j).length)
    (x : Fin ((rankCastRightRefinement C A B hC hA hB j).size k)) :
    ((twoBlocks (C + A) B (Nat.add_pos_left hC A) hB).rankCast (Nat.add_assoc C A B)).index j
        ((rankCastRightRefinement C A B hC hA hB j).index k x) =
      (threeBlocks C A B hC hA hB).index (rankCastRightLabelEquiv C A B hC hA hB ⟨j, k⟩)
        (Fin.cast (rankCastRightLabelEquiv_size C A B hC hA hB ⟨j, k⟩) x) :=
  BlockShape.index_index_eq_of_lex (threeBlocks C A B hC hA hB)
    ((twoBlocks (C + A) B (Nat.add_pos_left hC A) hB).rankCast (Nat.add_assoc C A B))
    (rankCastRightRefinement C A B hC hA hB) (rankCastRightLabelEquiv C A B hC hA hB)
    (rankCastRightLabelEquiv_size C A B hC hA hB) (rightLabelEquiv_lex C A B hC hA hB) j k x

end Langlands.Parabolic
