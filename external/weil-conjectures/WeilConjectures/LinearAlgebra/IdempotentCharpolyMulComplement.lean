/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.LinearAlgebra.IdempotentCharpoly
import Mathlib.Tactic.NoncommRing

/-! # Multiplicativity of complementary idempotent determinant polynomials

Source: Stacks Project, Tag 09XI, proof of (3)⇒(1).
(blueprint: lem-weil-pbc-idempotent-charpoly-mul-complement)
-/

@[expose] public section

universe u v

namespace Matrix

variable {A : Type u} [CommRing A] {n : Type v} [Fintype n] [DecidableEq n]

/-- The two complementary determinant factors multiply to the ambient characteristic
polynomial. Source: Stacks Project, Tag 09XI, proof of (3)⇒(1).
(blueprint: lem-weil-pbc-idempotent-charpoly-mul-complement)
Proof: put Q=1-P. The characteristic matrix commutes with P, P²=P, and PQ=QP=0.
Thus `(Q+(X-T)P)(P+(X-T)Q)=X-T`. Take determinants. -/
theorem idempotentCharpoly_mul_complement (T P : Matrix n n A)
    (hP : P * P = P) (hTP : T * P = P * T) :
    idempotentCharpoly T P * idempotentCharpoly T (1 - P) = T.charpoly := by
  let p := Polynomial.C.mapMatrix P
  let c := T.charmatrix
  have hp : p * p = p := by
    dsimp [p]
    rw [← map_mul, hP]
  have hcp : c * p = p * c := by
    dsimp [c, charmatrix, p]
    rw [sub_mul, mul_sub, ← map_mul, ← map_mul, hTP]
    congr 1
    exact (scalar_commute _ (fun _ ↦ Commute.all _ _) _).eq
  have hpcp : p * c * p = p * c := by
    rw [mul_assoc, hcp, ← mul_assoc, hp]
  have hprod : (1 - p + c * p) * (1 - (1 - p) + c * (1 - p)) = c := by
    noncomm_ring [← mul_assoc, hcp, hp, hpcp]
  unfold idempotentCharpoly charpoly
  rw [map_sub, map_one, ← det_mul]
  exact congrArg det hprod


end Matrix
