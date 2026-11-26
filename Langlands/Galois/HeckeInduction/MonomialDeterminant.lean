import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Reciprocal characteristic polynomials of weighted permutation matrices

For a self-map `π` of a finite set `Q` and weights `c : Q → R`, the matrix with entry `c q` in
position `(q, π q)` and zero elsewhere is a weighted permutation matrix when the orbits of `π`
are cycles. `det_one_sub_X_smul_monomial` computes `det (1 - X M)` as the product over the
cycles of `1 - (∏ c) X ^ length`, given the cycles as base points and lengths whose iterates
enumerate `Q` without repetition. The single-cycle case `det_one_sub_X_smul_cycleShift` is a
Laplace expansion along the last row; the general case reindexes by the cycles and uses the
block-triangular determinant formula.
-/

noncomputable section

open Polynomial Matrix

namespace Langlands.MonomialDeterminant

variable {R : Type*} [CommRing R]

/-- The weighted cyclic shift on `Fin m`: row `k` has the entry `d k` in column `k + 1`,
taken modulo `m`. -/
def cycleShift {m : ℕ} (d : Fin m → R) : Matrix (Fin m) (Fin m) R :=
  Matrix.of fun k k' => if finRotate m k = k' then d k else 0

theorem cycleShift_apply {m : ℕ} (d : Fin m → R) (k k' : Fin m) :
    cycleShift d k k' = if finRotate m k = k' then d k else 0 := rfl

private theorem entry_apply {m : ℕ} (d : Fin m → R) (k k' : Fin m) :
    (1 - (X : R[X]) • (cycleShift d).map C : Matrix (Fin m) (Fin m) R[X]) k k' =
      (if k = k' then 1 else 0) - X * (if finRotate m k = k' then C (d k) else 0) := by
  rw [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply, cycleShift_apply,
    smul_eq_mul]
  congr 2
  split_ifs <;> simp

private theorem val_finRotate_castSucc {n : ℕ} (i : Fin (n + 1)) :
    ((finRotate (n + 2) (Fin.castSucc i) : Fin (n + 2)) : ℕ) = i + 1 := by
  rw [coe_finRotate_of_ne_last (Fin.castSucc_lt_last i).ne, Fin.val_castSucc]

theorem det_one_sub_X_smul_cycleShift_succ (n : ℕ) (d : Fin (n + 1) → R) :
    det (1 - (X : R[X]) • (cycleShift d).map C) = 1 - C (∏ k, d k) * X ^ (n + 1) := by
  rcases n with _ | n
  · have h0 : finRotate (0 + 1) 0 = 0 := Fin.ext (by simp)
    rw [det_fin_one, entry_apply, h0, ite_eq_left rfl, ite_eq_left rfl, Fin.prod_univ_one]
    ring
  set A : Matrix (Fin (n + 2)) (Fin (n + 2)) R[X] := 1 - (X : R[X]) • (cycleShift d).map C
    with hA
  have hrow (j : Fin (n + 2)) :
      A (Fin.last _) j = (if Fin.last _ = j then 1 else 0) -
        X * (if (0 : Fin (n + 2)) = j then C (d (Fin.last _)) else 0) := by
    rw [hA, entry_apply, finRotate_last]
  have hlast0 : (Fin.last (n + 1) : Fin (n + 2)) ≠ 0 := Fin.last_pos.ne'
  rw [det_succ_row A (Fin.last _), Fintype.sum_eq_add 0 (Fin.last _) hlast0.symm]
  swap
  · intro j hj
    rw [hrow, ite_eq_right (Ne.symm hj.2), ite_eq_right (Ne.symm hj.1)]
    simp
  have hupper : det (A.submatrix (Fin.last (n + 1)).succAbove (Fin.last (n + 1)).succAbove) =
      1 := by
    rw [det_of_isUpperTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      rw [Fin.succAbove_last, submatrix_apply, hA, entry_apply, ite_eq_left rfl, ite_eq_right]
      · simp
      · intro h
        have := congrArg Fin.val h
        rw [val_finRotate_castSucc, Fin.val_castSucc] at this
        omega
    · intro i j hij
      have hij' : (j : ℕ) < i := hij
      rw [Fin.succAbove_last, submatrix_apply, hA, entry_apply, ite_eq_right, ite_eq_right]
      · simp
      · intro h
        have := congrArg Fin.val h
        rw [val_finRotate_castSucc, Fin.val_castSucc] at this
        omega
      · intro h
        have := congrArg Fin.val h
        rw [Fin.val_castSucc, Fin.val_castSucc] at this
        omega
  have hlower : det (A.submatrix (Fin.last (n + 1)).succAbove (0 : Fin (n + 2)).succAbove) =
      ∏ i : Fin (n + 1), (-(X : R[X]) * C (d (Fin.castSucc i))) := by
    rw [det_of_isLowerTriangular]
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [Fin.succAbove_last, Fin.succAbove_zero, submatrix_apply, hA, entry_apply,
        ite_eq_right, ite_eq_left]
      · ring
      · apply Fin.ext
        rw [val_finRotate_castSucc, Fin.val_succ]
      · intro h
        have := congrArg Fin.val h
        rw [Fin.val_castSucc, Fin.val_succ] at this
        omega
    · intro i j hij
      have hij' : (i : ℕ) < j := hij
      rw [Fin.succAbove_last, Fin.succAbove_zero, submatrix_apply, hA, entry_apply,
        ite_eq_right, ite_eq_right]
      · simp
      · intro h
        have := congrArg Fin.val h
        rw [val_finRotate_castSucc, Fin.val_succ] at this
        omega
      · intro h
        have := congrArg Fin.val h
        rw [Fin.val_castSucc, Fin.val_succ] at this
        omega
  rw [hupper, hlower, hrow, hrow, ite_eq_right hlast0, ite_eq_left rfl, ite_eq_left rfl,
    ite_eq_right hlast0.symm]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← map_prod, Fin.prod_univ_castSucc (f := d), map_mul]
  simp only [Fin.val_last, Fin.val_zero, add_zero]
  have h2 : ((-1 : R[X]) ^ (n + 1 + (n + 1))) = 1 := by
    rw [← two_mul, pow_mul, neg_one_sq, one_pow]
  have h3 : (-1 : R[X]) ^ (n + 1) * (-(X : R[X])) ^ (n + 1) = X ^ (n + 1) := by
    rw [← mul_pow, neg_one_mul, neg_neg]
  rw [h2]
  have h4 : (-1 : R[X]) ^ (n + 1) * (0 - X * C (d (Fin.last (n + 1)))) *
      ((-X) ^ (n + 1) * C (∏ i : Fin (n + 1), d (Fin.castSucc i))) =
      -(X * C (d (Fin.last (n + 1))) * C (∏ i : Fin (n + 1), d (Fin.castSucc i))) *
        ((-1) ^ (n + 1) * (-X) ^ (n + 1)) := by ring
  rw [h4, h3]
  ring

theorem det_one_sub_X_smul_cycleShift {m : ℕ} (hm : 0 < m) (d : Fin m → R) :
    det (1 - (X : R[X]) • (cycleShift d).map C) = 1 - C (∏ k, d k) * X ^ m := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  exact det_one_sub_X_smul_cycleShift_succ n d

theorem val_finRotate {m : ℕ} (k : Fin m) : (finRotate m k : ℕ) = (k + 1) % m := by
  rcases m with _ | n
  · exact k.elim0
  rw [coe_finRotate]
  split_ifs with h
  · subst h
    simp
  · have : (k : ℕ) < n := Fin.val_lt_last h
    rw [Nat.mod_eq_of_lt (by omega)]

/-- **Weighted permutation matrices.** Let `π` be a self-map of a finite set `Q` whose
orbits are the cycles `base w, π (base w), …, π^[len w - 1] (base w)`, one for each `w`,
listed without repetition and covering `Q`. For the matrix with entry `c q` in position
`(q, π q)` and zero elsewhere, `det (1 - X M)` is the product over the cycles of
`1 - (∏ c) X ^ len`. -/
theorem det_one_sub_X_smul_monomial {Q W : Type*} [Fintype Q] [DecidableEq Q] [Fintype W]
    (π : Q → Q) (c : Q → R) (base : W → Q) (len : W → ℕ) (hlen : ∀ w, 0 < len w)
    (hcycle : ∀ w, π^[len w] (base w) = base w)
    (hbij : Function.Bijective (fun i : Σ w, Fin (len w) => π^[i.2] (base i.1))) :
    det (1 - (X : R[X]) •
        (Matrix.of fun q q' => if π q = q' then c q else 0 : Matrix Q Q R).map C) =
      ∏ w, (1 - C (∏ k : Fin (len w), c (π^[k] (base w))) * X ^ len w) := by
  classical
  let : LinearOrder W := LinearOrder.lift' (Fintype.equivFin W) (Fintype.equivFin W).injective
  let e : (Σ w, Fin (len w)) ≃ Q := Equiv.ofBijective _ hbij
  have he (i : Σ w, Fin (len w)) : e i = π^[i.2] (base i.1) := rfl
  have hπ (i : Σ w, Fin (len w)) : π (e i) = e ⟨i.1, finRotate _ i.2⟩ := by
    rw [he, he, ← Function.iterate_succ_apply' π]
    have hper : Function.IsPeriodicPt π (len i.1) (base i.1) := hcycle i.1
    rw [← hper.iterate_mod_apply, val_finRotate]
  set A : Matrix Q Q R[X] := 1 - (X : R[X]) •
    (Matrix.of fun q q' => if π q = q' then c q else 0 : Matrix Q Q R).map C with hA
  have hB (i j : Σ w, Fin (len w)) : A.submatrix e e i j =
      (if i = j then 1 else 0) -
        X * (if (⟨i.1, finRotate _ i.2⟩ : Σ w, Fin (len w)) = j then C (c (e i)) else 0) := by
    rw [submatrix_apply, hA, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.of_apply, smul_eq_mul, hπ]
    simp only [e.injective.eq_iff]
    congr 2
    split_ifs <;> simp
  have hblock : (A.submatrix e e).BlockTriangular Sigma.fst := by
    intro i j hij
    have hne : i.1 ≠ j.1 := ne_of_gt hij
    have h1 : i ≠ j := fun h => hne (congrArg Sigma.fst h)
    have h2 : (⟨i.1, finRotate _ i.2⟩ : Σ w, Fin (len w)) ≠ j :=
      fun h => hne (congrArg Sigma.fst h : (⟨i.1, finRotate _ i.2⟩ : Σ w, Fin (len w)).1 = j.1)
    rw [hB, ite_eq_right h1, ite_eq_right h2]
    simp
  rw [← det_submatrix_equiv_self e, hblock.det,
    Finset.image_univ_of_surjective (fun w => ⟨⟨w, ⟨0, hlen w⟩⟩, rfl⟩)]
  refine Finset.prod_congr rfl fun w _ => ?_
  let φ : Fin (len w) ≃ {i : Σ w, Fin (len w) // i.1 = w} := (Equiv.sigmaSubtype (β := fun w => Fin (len w)) w).symm
  have hφ (k : Fin (len w)) : (φ k : Σ w, Fin (len w)) = ⟨w, k⟩ := rfl
  rw [← det_submatrix_equiv_self φ]
  have hsq : ((A.submatrix e e).toSquareBlock Sigma.fst w).submatrix φ φ =
      1 - (X : R[X]) • (cycleShift fun k : Fin (len w) => c (e ⟨w, k⟩)).map C := by
    ext k k'
    rw [entry_apply, submatrix_apply, toSquareBlock_def, of_apply, hB, hφ, hφ]
    simp only [(sigma_mk_injective (i := w)).eq_iff]
  rw [hsq, det_one_sub_X_smul_cycleShift (hlen w)]
  rfl

end Langlands.MonomialDeterminant
