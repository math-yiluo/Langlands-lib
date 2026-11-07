import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.LocalRing.Basic

/-! # Zero detection for idempotent matrices over a local ring -/

namespace Langlands.LinearAlgebra

universe u v w z

variable {R : Type u} {A : Type v} {n : Type w}
  [CommRing R] [IsLocalRing R] [CommRing A] [Nontrivial A]
  [Fintype n] [DecidableEq n]

/-- A scalar extension to a nontrivial commutative ring detects zero idempotent matrices. -/
theorem idempotent_matrix_map_eq_zero_iff (f : R →+* A) (P : Matrix n n R)
    (hP : P * P = P) : P.map f = 0 ↔ P = 0 := by
  constructor
  · intro hmap
    have hdet : f (1 - P).det = 1 := by
      rw [f.map_det]
      have hmatrix : f.mapMatrix (1 - P) = 1 := by
        rw [map_sub, map_one]
        change 1 - P.map f = 1
        rw [hmap, sub_zero]
      rw [hmatrix, Matrix.det_one]
    have hnunit : 1 - (1 - P).det ∈ nonunits R := by
      intro hu
      have hu' := hu.map f
      have hz : f (1 - (1 - P).det) = 0 := by
        rw [map_sub, map_one, hdet, sub_self]
      rw [hz] at hu'
      exact not_isUnit_zero hu'
    have hunit : IsUnit (1 - P : Matrix n n R) :=
      (Matrix.isUnit_iff_isUnit_det _).2
        (IsLocalRing.isUnit_of_mem_nonunits_one_sub_self _ hnunit)
    apply hunit.mul_right_eq_zero.mp
    rw [sub_mul, one_mul, hP, sub_self]
  · rintro rfl
    ext i j
    exact f.map_zero

/-- Nonvanishing of an idempotent matrix is preserved by every such scalar extension. -/
theorem idempotent_matrix_map_ne_zero_iff (f : R →+* A) (P : Matrix n n R)
    (hP : P * P = P) : P.map f ≠ 0 ↔ P ≠ 0 :=
  not_congr (idempotent_matrix_map_eq_zero_iff f P hP)

/-- Two scalar extensions to nontrivial rings have exactly the same nonzero idempotents. -/
theorem idempotent_matrix_map_ne_zero_iff_map {B : Type z}
    [CommRing B] [Nontrivial B] (f : R →+* A) (g : R →+* B)
    (P : Matrix n n R) (hP : P * P = P) : P.map f ≠ 0 ↔ P.map g ≠ 0 :=
  (idempotent_matrix_map_ne_zero_iff f P hP).trans
    (idempotent_matrix_map_ne_zero_iff g P hP).symm

/-- A family of idempotent projectors has a common nonzero support on all nontrivial fibres. -/
theorem idempotent_matrix_family_support_map {ι : Type*}
    (f : R →+* A) (P : ι → Matrix n n R) (hP : ∀ i, P i * P i = P i) :
    {i | (P i).map f ≠ 0} = {i | P i ≠ 0} := by
  ext i
  exact idempotent_matrix_map_ne_zero_iff f (P i) (hP i)

/-- Identify the occurring indices of a family of projectors before and after scalar extension. -/
def idempotentMatrixSupportEquiv {ι : Type*}
    (f : R →+* A) (P : ι → Matrix n n R) (hP : ∀ i, P i * P i = P i) :
    {i // P i ≠ 0} ≃ {i // (P i).map f ≠ 0} where
  toFun i := ⟨i.1, (idempotent_matrix_map_ne_zero_iff f (P i.1) (hP i.1)).2 i.2⟩
  invFun i := ⟨i.1, (idempotent_matrix_map_ne_zero_iff f (P i.1) (hP i.1)).1 i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem idempotentMatrixSupportEquiv_apply {ι : Type*}
    (f : R →+* A) (P : ι → Matrix n n R) (hP : ∀ i, P i * P i = P i)
    (i : {i // P i ≠ 0}) : (idempotentMatrixSupportEquiv f P hP i).1 = i.1 := rfl

@[simp]
theorem idempotentMatrixSupportEquiv_symm_apply {ι : Type*}
    (f : R →+* A) (P : ι → Matrix n n R) (hP : ∀ i, P i * P i = P i)
    (i : {i // (P i).map f ≠ 0}) :
    ((idempotentMatrixSupportEquiv f P hP).symm i).1 = i.1 := rfl

end Langlands.LinearAlgebra
