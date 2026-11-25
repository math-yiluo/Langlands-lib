/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Invertible matrices: size at most one, and Kronecker products

Invertible matrices indexed by a subsingleton type commute. The Kronecker product of invertible
matrices is a homomorphism `GL n R × GL m R →* GL (n × m) R`, natural in the ring `R`.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

/-- Invertible matrices of size at most one commute. -/
theorem mul_comm_of_subsingleton {n R : Type*} [Fintype n] [DecidableEq n] [Subsingleton n]
    [CommRing R] (g h : GL n R) : g * h = h * g := by
  ext i j
  simp only [Units.val_mul, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  obtain rfl := Subsingleton.elim l i
  obtain rfl := Subsingleton.elim j l
  exact mul_comm _ _

section kronecker

open scoped Kronecker

variable {n m R : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [CommRing R]

/-- The Kronecker product of invertible matrices, as a homomorphism
`GL n R × GL m R →* GL (n × m) R`. -/
def kroneckerHom : GL n R × GL m R →* GL (n × m) R where
  toFun g := GeneralLinearGroup.kronecker g.1 g.2
  map_one' := Units.ext one_kronecker_one
  map_mul' _ _ := Units.ext (mul_kronecker_mul _ _ _ _)

@[simp]
theorem coe_kroneckerHom (g : GL n R × GL m R) :
    (kroneckerHom g : Matrix (n × m) (n × m) R) = (g.1 : Matrix n n R) ⊗ₖ (g.2 : Matrix m m R) :=
  rfl

/-- The Kronecker product of invertible matrices is natural in the ring of coefficients. -/
theorem kroneckerHom_map {S : Type*} [CommRing S] (f : R →+* S) (g : GL n R × GL m R) :
    kroneckerHom (map f g.1, map f g.2) = map f (kroneckerHom g) := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  simp [Matrix.kroneckerMap_apply]

end kronecker

end Matrix.GeneralLinearGroup
