/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.RingTheory.Ideal.Span
import Mathlib.LinearAlgebra.Matrix.Adjugate
import WeilConjectures.LinearAlgebra.Matrix.CauchyBinet

/-!
# Scalar left inverses and maximal minors

Source: Stacks Project, Algebra, Lemma 07DQ and the Cauchy–Binet formula 0F0K
(blueprint: lem-weil-pbc-matrix-left-inverse-minors).
-/

@[expose] public section

universe u

namespace Matrix

/-- The ideal of maximal row minors gives scalar left inverses, and a scalar left inverse
puts the `m`-th power of its scalar in that ideal, with the explicit Cauchy–Binet expression.
Source: Stacks Project, Algebra, Lemma 07DQ and item 0F0K
(blueprint: lem-weil-pbc-matrix-left-inverse-minors).

Each subset of size `m` is enumerated in increasing order by `orderEmbOfFin`. The ideal is
written using `Ideal.span` of the range of these determinants. For `m = 0` the unique subset
is empty, its determinant is one, and this ideal is the whole ring.

Proof (the four steps of the node):
1. For each subset `I`, let `E_I` be the projection matrix selecting its rows. Entrywise
   multiplication gives `E_I * A = A_I` (def-weil-matrix, def-weil-submatrix).
2. For `f` in the span, write `f = ∑ I, c_I * det A_I`. Put
   `B = ∑ I, c_I • (adjugate A_I * E_I)`. The identity
   `adjugate A_I * A_I = det A_I • 1` (lem-weil-pbc-matrix-adjugate-identity)
   gives `B * A = f • 1`. For zero columns all these matrices are empty.
3. If `B * A = f • 1`, take determinants. The Leibniz expansion of the diagonal matrix
   `f • 1` gives `det (B * A) = f ^ m`, also for `m = 0` when both sides are one.
4. Apply lem-weil-pbc-cauchy-binet to `B` and `A`: the determinant of the product is the
   sum of the products of their corresponding column and row minors. These column minors
   are precisely the coefficients in the stated formula. It is an ideal combination of
   the generators, so `f ^ m` belongs to the span. -/
theorem scalar_left_inverse_maximal_minors {R : Type u} [CommRing R]
    (n m : ℕ) (_hmn : m ≤ n) (A : Matrix (Fin n) (Fin m) R) :
    let J : Ideal R := Ideal.span (Set.range
      (fun I : {I : Finset (Fin n) // I.card = m} ↦
        (A.submatrix (I.val.orderEmbOfFin I.property) id).det))
    (∀ f : R, f ∈ J → ∃ B : Matrix (Fin m) (Fin n) R, B * A = f • 1) ∧
      (∀ (f : R) (B : Matrix (Fin m) (Fin n) R), B * A = f • 1 →
        f ^ m ∈ J ∧
          f ^ m = ∑ I : {I : Finset (Fin n) // I.card = m},
            (B.submatrix id (I.val.orderEmbOfFin I.property)).det *
              (A.submatrix (I.val.orderEmbOfFin I.property) id).det) := by
  classical
  dsimp only
  constructor
  · intro f hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro x ⟨I, rfl⟩
      let e : Fin m → Fin n := I.val.orderEmbOfFin I.property
      refine ⟨(A.submatrix e id).adjugate * (1 : Matrix (Fin n) (Fin n) R).submatrix
        e id, ?_⟩
      have hproj : (1 : Matrix (Fin n) (Fin n) R).submatrix e id * A =
          A.submatrix e id := by
        simpa using one_submatrix_mul e (Equiv.refl (Fin n)) A
      rw [Matrix.mul_assoc, hproj, adjugate_mul]
    · exact ⟨0, by simp⟩
    · intro x y _ _ hx hy
      obtain ⟨B, hB⟩ := hx
      obtain ⟨C, hC⟩ := hy
      exact ⟨B + C, by rw [Matrix.add_mul, hB, hC, add_smul]⟩
    · intro r x _ hx
      obtain ⟨B, hB⟩ := hx
      exact ⟨r • B, by simp only [smul_mul, hB, smul_smul, smul_eq_mul]⟩
  · intro f B hB
    have hdet : (B * A).det = f ^ m := by
      rw [hB, det_smul, det_one, Fintype.card_fin, mul_one]
    have hsum := (cauchy_binet m n B A).1
    rw [hdet] at hsum
    refine ⟨?_, hsum⟩
    rw [hsum]
    apply Submodule.sum_mem
    intro I _
    apply Ideal.mul_mem_left
    exact Ideal.subset_span ⟨I, rfl⟩

end Matrix
