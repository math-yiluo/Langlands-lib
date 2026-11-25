/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block

/-! # The coordinate equations of a triangular Weil flag

Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, dimension-zero
Jordan-filtration sub-step
(blueprint: lem-zl-condensed-point-weil-flags-block-equations).
-/

@[expose] public section
set_option autoImplicit false
universe u
namespace WeilConjectures.CondensedWeilPointFlags

/-- Coordinate inclusion intertwines successive leading blocks, and last-coordinate
projection intertwines the larger block with its final diagonal scalar.
Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, dimension-zero
Jordan-filtration sub-step
(blueprint: lem-zl-condensed-point-weil-flags-block-equations).

Proof: multiplying by the inclusion selects the first columns. On a nonfinal row the
result agrees with the smaller block; on the final row its entries vanish by upper
triangularity. Multiplying by the projection selects the last row, all of whose entries
except the last vanish. The remaining entry is the specified diagonal scalar.
The argument includes the rank-zero smaller block. -/
theorem leading_block_equations {K : Type u} [Field K] {d : ℕ}
    (C : Matrix (Fin d) (Fin d) K) (hC : C.IsUpperTriangular) (j : Fin d) :
    let Cj := C.submatrix (Fin.castLE (Nat.le_of_lt j.isLt))
      (Fin.castLE (Nat.le_of_lt j.isLt))
    let Cj1 := C.submatrix (Fin.castLE (Nat.succ_le_of_lt j.isLt))
      (Fin.castLE (Nat.succ_le_of_lt j.isLt))
    let I : Matrix (Fin (j.val + 1)) (Fin j.val) K :=
      fun r k ↦ if r = k.castSucc then 1 else 0
    let π : Matrix (Fin 1) (Fin (j.val + 1)) K :=
      fun _ k ↦ if k = Fin.last j.val then 1 else 0
    Cj1 * I = I * Cj ∧ π * Cj1 = C j j • π := by
  classical
  dsimp only
  constructor
  · ext r k
    simp only [Matrix.mul_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    refine Fin.lastCases ?_ (fun r ↦ ?_) r
    · have hz : C (Fin.castLE (Nat.succ_le_of_lt j.isLt) (Fin.last j.val))
          (Fin.castLE (Nat.succ_le_of_lt j.isLt) k.castSucc) = 0 :=
        hC (show k.val < j.val from k.isLt)
      have hz' : C (Fin.castLE (Nat.succ_le_of_lt j.isLt) (Fin.last j.val))
          (Fin.castLE (Nat.le_of_lt j.isLt) k) = 0 := hz
      simp [Matrix.submatrix_apply, hz',
        (fun (x : Fin j.val) ↦ (Fin.castSucc_ne_last x).symm)]
    · simp [Matrix.submatrix_apply, Fin.castSucc_inj, ite_mul]
  · ext r k
    simp only [Matrix.mul_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    refine Fin.lastCases ?_ (fun k ↦ ?_) k
    · have he : Fin.castLE (Nat.succ_le_of_lt j.isLt) (Fin.last j.val) = j := by
        apply Fin.ext
        rfl
      simp [Matrix.submatrix_apply, Matrix.smul_apply, he, smul_eq_mul]
    · have hz : C (Fin.castLE (Nat.succ_le_of_lt j.isLt) (Fin.last j.val))
          (Fin.castLE (Nat.succ_le_of_lt j.isLt) k.castSucc) = 0 :=
        hC (show k.val < j.val from k.isLt)
      simp only [Matrix.submatrix_apply, Matrix.smul_apply,
        ite_eq_right (Fin.castSucc_ne_last k), smul_eq_mul, mul_zero]
      exact hz

end WeilConjectures.CondensedWeilPointFlags
