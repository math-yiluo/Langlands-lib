/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import WeilConjectures.LinearAlgebra.Matrix.CauchyBinet
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Nonzero maximal minors of injective matrices over fields

Source: Stacks Project, Algebra, Tags 00MY, 00MW (1), (3), and 00MV, specialized to a field
(blueprint: lem-weil-pbc-field-injective-matrix-nonzero-maximal-minor).
-/

@[expose] public section

universe u

namespace Matrix

/-- An injective `p × n` matrix over a field has `n ≤ p` and a nonzero maximal minor on
an increasing selection of rows and all columns. For zero columns the row selection is
empty and its determinant is one.

Source: Stacks Project, Algebra, Tags 00MY, 00MW (1), (3), and 00MV, specialized to a field
(blueprint: lem-weil-pbc-field-injective-matrix-nonzero-maximal-minor).

Proof (the node's agent argument using Stacks, Tag 0F0K, Cauchy--Binet):
1. The map `v ↦ B.mulVec v` is linear by distributivity of finite sums and injective by
hypothesis. Apply lem-weil-pbc-injective-coordinate-linear-map-retraction to obtain a
linear retraction `g : K^p → K^n`.
2. Define `C j i = g(e_i) j` for the coordinate unit vectors `e_i` of `K^p`
(def-weil-matrix). Expanding any vector in these unit vectors shows that `g` is given by
multiplication by `C`. Evaluating `g(B ε_k) = ε_k` gives `C * B = 1`, including `n = 0`.
3. The Leibniz formula (def-weil-pbc-matrix-determinant) gives `det 1 = 1`. Apply
lem-weil-pbc-cauchy-binet to express `det (C * B)` as the sum over all `n`-element subsets
of the `p` indices of the products of the corresponding column minor of `C` and row
minor of `B`, both in increasing order. This formula does not assume `n ≤ p`.
4. If every row minor vanished, the sum would be zero, contradicting `1 ≠ 0` in the field
(def-weil-field). Thus an `n`-element subset has nonzero row-minor determinant and its
cardinality gives `n ≤ p`. Enumerating its rows increasingly gives the submatrix
(def-weil-submatrix) below. For `n = 0` the subset is empty and the empty-product
convention in def-weil-pbc-matrix-determinant gives determinant one. -/
theorem exists_strictMono_submatrix_det_ne_zero_of_mulVec_injective
    {K : Type u} [Field K] {n p : ℕ} (B : Matrix (Fin p) (Fin n) K)
    (hinj : Function.Injective B.mulVec) :
    n ≤ p ∧ ∃ r : Fin n → Fin p, StrictMono r ∧
      (B.submatrix r id).det ≠ 0 ∧ (n = 0 → (B.submatrix r id).det = 1) := by
  classical
  obtain ⟨g, hg⟩ := B.toLin'.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  let C : Matrix (Fin n) (Fin p) K := LinearMap.toMatrix' g
  have hCB : C * B = 1 := by
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_id] using congrArg LinearMap.toMatrix' hg
  have hsum := (cauchy_binet n p C B).1
  rw [hCB, det_one] at hsum
  have hex : ∃ S : {S : Finset (Fin p) // S.card = n},
      (B.submatrix (S.val.orderEmbOfFin S.property) id).det ≠ 0 := by
    by_contra h
    push Not at h
    have hz : (∑ S : {S : Finset (Fin p) // S.card = n},
        (C.submatrix id (S.val.orderEmbOfFin S.property)).det *
          (B.submatrix (S.val.orderEmbOfFin S.property) id).det) = 0 := by
      apply Finset.sum_eq_zero
      intro S _
      rw [h S, mul_zero]
    exact one_ne_zero (hsum.trans hz)
  obtain ⟨S, hS⟩ := hex
  have hnp : n ≤ p := by
    simpa only [S.property, Fintype.card_fin] using Finset.card_le_univ S.val
  refine ⟨hnp, S.val.orderEmbOfFin S.property,
    (S.val.orderEmbOfFin S.property).strictMono, hS, ?_⟩
  intro hn
  subst n
  simp

end Matrix
