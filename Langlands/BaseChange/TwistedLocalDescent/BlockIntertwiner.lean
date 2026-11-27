import Langlands.BaseChange.LeviNormDescent

/-! # Intertwiners of block upper triangular matrices with coprime diagonal blocks

Over a field, if `g p = p' g` for block upper triangular matrices `p, p'` such that, whenever
`k ≠ i`, the `k`-th diagonal block of `p'` and the `i`-th diagonal block of `p` have coprime
characteristic polynomials, then `g` is block upper triangular. See the paired Markdown.
-/

namespace Langlands.BaseChange.TwistedLocalDescent

open Langlands.GeneralLinear
open _root_.Polynomial

universe u

/-- A rectangular intertwiner `A X = X C` between square matrices with coprime characteristic
polynomials vanishes. -/
theorem intertwiner_eq_zero {R : Type u} [Field R] {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) R) (C : Matrix (Fin b) (Fin b) R)
    (X : Matrix (Fin a) (Fin b) R) (h : A * X = X * C)
    (hAC : IsCoprime A.charpoly C.charpoly) : X = 0 := by
  have hLin : A.mulVecLin.comp X.mulVecLin = X.mulVecLin.comp C.mulVecLin := by
    simpa only [Matrix.mulVecLin_mul] using congrArg Matrix.mulVecLin h
  have hA : aeval A.mulVecLin A.charpoly = 0 := by
    rw [← Matrix.charpoly_mulVecLin]
    exact LinearMap.aeval_self_charpoly _
  have hC : aeval C.mulVecLin C.charpoly = 0 := by
    rw [← Matrix.charpoly_mulVecLin]
    exact LinearMap.aeval_self_charpoly _
  have hzero : (aeval A.mulVecLin C.charpoly).comp X.mulVecLin = 0 := by
    rw [Langlands.LinearAlgebra.aeval_intertwines X.mulVecLin hLin, hC, LinearMap.comp_zero]
  obtain ⟨p, q, hpq⟩ := hAC
  have hOne : aeval A.mulVecLin q * aeval A.mulVecLin C.charpoly = 1 := by
    have he := congrArg (aeval A.mulVecLin) hpq
    simpa only [map_add, map_mul, map_one, hA, mul_zero, zero_add] using he
  apply Matrix.toLin'.injective
  change X.mulVecLin = (0 : Matrix (Fin a) (Fin b) R).mulVecLin
  rw [show (0 : Matrix (Fin a) (Fin b) R).mulVecLin = 0 by exact Matrix.toLin'.map_zero]
  calc
    X.mulVecLin = (1 : Module.End R (Fin a → R)).comp X.mulVecLin :=
      (LinearMap.id_comp _).symm
    _ = 0 := by
      rw [← hOne, Module.End.mul_eq_comp, LinearMap.comp_assoc, hzero, LinearMap.comp_zero]

variable {R : Type u} [Field R] {n : ℕ} (B : BlockShape n)

/-- The `(i, j)` block of a square matrix. -/
def block (A : Matrix (Fin n) (Fin n) R) (i j : Fin B.length) :
    Matrix (Fin (B.size i)) (Fin (B.size j)) R :=
  A.submatrix (B.index i) (B.index j)

/-- A matrix is block upper triangular when its blocks strictly below the diagonal vanish. -/
def IsBlockUpper (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ (i j : Fin B.length) (a : Fin (B.size i)) (b : Fin (B.size j)), j < i →
    A (B.index i a) (B.index j b) = 0

theorem isBlockUpper_iff_mem_parabolic (g : GeneralLinear n R) :
    IsBlockUpper B g.val ↔ g ∈ B.parabolic R :=
  (B.mem_parabolic_iff R g).symm

/-- Entries of a product, summed block by block. -/
theorem mul_apply_index (A C : Matrix (Fin n) (Fin n) R) (i j : Fin B.length)
    (a : Fin (B.size i)) (b : Fin (B.size j)) :
    (A * C) (B.index i a) (B.index j b) =
      ∑ l : Fin B.length, ∑ t : Fin (B.size l),
        A (B.index i a) (B.index l t) * C (B.index l t) (B.index j b) := by
  rw [Matrix.mul_apply, ← Equiv.sum_comp B.indexEquiv]
  simp only [← Finset.univ_sigma_univ, Finset.sum_sigma]
  rfl

/-- **Block intertwiner lemma.** Let `A` and `C` be block upper triangular and `G A = C G`. If
for all distinct block indices `k ≠ i` the characteristic polynomials of the diagonal blocks
`C_kk` and `A_ii` are coprime, then `G` is block upper triangular. -/
theorem isBlockUpper_of_mul_eq {A C G : Matrix (Fin n) (Fin n) R}
    (hA : IsBlockUpper B A) (hC : IsBlockUpper B C) (h : G * A = C * G)
    (hcop : ∀ i k : Fin B.length, i ≠ k →
      IsCoprime (block B C k k).charpoly (block B A i i).charpoly) :
    IsBlockUpper B G := by
  -- Strong induction on `i + (length - k)` over pairs `i < k`.
  suffices H : ∀ N : ℕ, ∀ (k i : Fin B.length), i < k → i.val + (B.length - k.val) ≤ N →
      block B G k i = 0 by
    intro k i a b hik
    have := H _ k i hik le_rfl
    exact congrFun (congrFun this a) b
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro k i hik hN
  -- Blocks in the same row farther left and in the same column farther down vanish.
  have hleft : ∀ l : Fin B.length, l < i → block B G k l = 0 := fun l hl =>
    ih (l.val + (B.length - k.val)) (by omega) k l (hl.trans hik) le_rfl
  have hright : ∀ l : Fin B.length, k < l → block B G l i = 0 := fun l hl =>
    ih (i.val + (B.length - l.val)) (by omega) l i (hik.trans hl) le_rfl
  apply intertwiner_eq_zero (block B C k k) (block B A i i) (block B G k i) _ (hcop i k hik.ne)
  ext s t
  have he := congrFun (congrFun h (B.index k s)) (B.index i t)
  rw [mul_apply_index, mul_apply_index] at he
  rw [Fintype.sum_eq_single i, Fintype.sum_eq_single k] at he
  · simp only [Matrix.mul_apply, block, Matrix.submatrix_apply]
    exact he.symm
  · intro l hl
    apply Finset.sum_eq_zero
    intro w _
    rcases lt_or_gt_of_ne hl with hlk | hkl
    · rw [hC k l s w hlk, zero_mul]
    · have := congrFun (congrFun (hright l hkl) w) t
      simp only [block, Matrix.submatrix_apply, Matrix.zero_apply] at this
      rw [this, mul_zero]
  · intro l hl
    apply Finset.sum_eq_zero
    intro w _
    rcases lt_or_gt_of_ne hl with hli | hil
    · have := congrFun (congrFun (hleft l hli) s) w
      simp only [block, Matrix.submatrix_apply, Matrix.zero_apply] at this
      rw [this, zero_mul]
    · rw [hA l i w t hil, mul_zero]

end Langlands.BaseChange.TwistedLocalDescent
