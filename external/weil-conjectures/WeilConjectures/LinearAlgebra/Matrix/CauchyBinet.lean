/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The Cauchy–Binet formula

Source: Stacks Project, Algebra, Section 00AR, item 0F0K
(blueprint: lem-weil-pbc-cauchy-binet).
-/

@[expose] public section

universe u

namespace Matrix

/-- The Cauchy–Binet formula, including its empty-sum and zero-size cases.
Source: Stacks Project, Algebra, Section 00AR, item 0F0K
(blueprint: lem-weil-pbc-cauchy-binet).

The subsets of size `m` are enumerated once each. For each subset, `orderEmbOfFin` lists
its indices in increasing order, and the same list selects columns of `A` and rows of `B`.

Proof: use the standard basis of `R^n` and its induced basis on the `m`th exterior
power. The coordinate of the exterior product of the columns of `B` at an `m`-element
subset is the determinant of the corresponding rows of `B` (up to transpose).
Apply the alternating linear form determined by the rows of `A` to this basis expansion.
Its value on the column product is `det (A * B)` (up to transpose), and on each basis
vector is the corresponding column minor of `A` (up to transpose). Linearity gives the
sum of products of minors. If `n < m`, no subset of size `m` exists, so the sum and
hence the product determinant vanish. If `m = 0`, the product determinant is one,
and the main equality gives the same value for the sum. -/
theorem cauchy_binet {R : Type u} [CommRing R] (m n : ℕ)
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    let minors : R := ∑ S : {S : Finset (Fin n) // S.card = m},
      (A.submatrix id (S.val.orderEmbOfFin S.property)).det *
        (B.submatrix (S.val.orderEmbOfFin S.property) id).det
    (A * B).det = minors ∧
      (n < m → minors = 0 ∧ (A * B).det = 0) ∧
      (m = 0 → (A * B).det = 1 ∧ minors = 1) := by
  classical
  dsimp only
  have hmain : (A * B).det =
      ∑ S : {S : Finset (Fin n) // S.card = m},
        (A.submatrix id (S.val.orderEmbOfFin S.property)).det *
          (B.submatrix (S.val.orderEmbOfFin S.property) id).det := by
    let : Fintype (Set.powersetCard (Fin n) m) :=
      inferInstanceAs (Fintype {S : Finset (Fin n) // S.card = m})
    let b := Pi.basisFun R (Fin n)
    let e := b.exteriorPower m
    let v : Fin m → (Fin n → R) := fun i j => B j i
    let f : Fin m → Module.Dual R (Fin n → R) :=
      fun i => (LinearMap.proj i).comp A.toLin'
    let L := exteriorPower.alternatingMapToDual R (Fin n → R) m f
    have h := congrArg L (e.sum_repr (exteriorPower.ιMulti R m v))
    simp only [map_sum, map_smul, smul_eq_mul] at h
    have hleft : L (exteriorPower.ιMulti R m v) = (A * B).det := by
      rw [exteriorPower.alternatingMapToDual_apply_ιMulti]
      rw [← Matrix.det_transpose]
      congr 1
    rw [hleft] at h
    change (A * B).det = _
    rw [← h]
    apply Finset.sum_congr rfl
    intro S _
    rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti,
      exteriorPower.basis_apply]
    change _ * L (exteriorPower.ιMulti R m _) = _
    rw [exteriorPower.alternatingMapToDual_apply_ιMulti]
    simp only [Set.powersetCard.ofFinEmbEquiv_symm_apply, Module.Basis.coord_apply,
      Pi.basisFun_repr, Function.comp_apply, Pi.basisFun_apply, LinearMap.coe_comp,
      LinearMap.coe_proj, Function.eval, toLin'_apply, mulVec_single, MulOpposite.op_one,
      Pi.smul_apply, col_apply, one_smul, b, v, f]
    change (B.submatrix (S.val.orderEmbOfFin S.property) id).transpose.det *
        (A.submatrix id (S.val.orderEmbOfFin S.property)).transpose.det = _
    rw [det_transpose, det_transpose, mul_comm]
  refine ⟨hmain, ?_, ?_⟩
  · intro hnm
    have hempty : IsEmpty {S : Finset (Fin n) // S.card = m} := by
      refine ⟨fun S => ?_⟩
      have hcard := Finset.card_le_univ S.val
      rw [S.property, Fintype.card_fin] at hcard
      exact (Nat.not_le_of_gt hnm) hcard
    have hzero : (∑ S : {S : Finset (Fin n) // S.card = m},
        (A.submatrix id (S.val.orderEmbOfFin S.property)).det *
          (B.submatrix (S.val.orderEmbOfFin S.property) id).det) = 0 := by
      simp
    exact ⟨hzero, hmain.trans hzero⟩
  · intro hm
    subst m
    have hone : (A * B).det = 1 := by simp
    exact ⟨hone, hmain.symm.trans hone⟩

end Matrix
