/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Projection

/-!
# The rank of an idempotent matrix

For an idempotent square matrix `P` over a field, the ranks of `P` and of `1 - P` add up to the
size of the matrix: the image of `1 - P` is the kernel of `P`.
-/

@[expose] public section

namespace Matrix

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- For an idempotent matrix `P` over a field, `rank (1 - P) + rank P` is the size of `P`. -/
theorem rank_one_sub_add_rank_of_isIdempotentElem {P : Matrix n n K} (hP : IsIdempotentElem P) :
    (1 - P).rank + P.rank = Fintype.card n := by
  have hP' : IsIdempotentElem P.mulVecLin := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← mulVecLin_mul, hP.eq]
  have h : (1 - P).mulVecLin = 1 - P.mulVecLin := by
    refine LinearMap.ext fun v ↦ ?_
    simp
  rw [rank, rank, h, ← LinearMap.IsIdempotentElem.ker_eq_range_one_sub hP', add_comm,
    LinearMap.finrank_range_add_finrank_ker, Module.finrank_fintype_fun_eq_card]

end Matrix
