import Langlands.GroupScheme.Examples.HermitianMatrixPairing

/-! # Gram coordinates and nondegeneracy of the actual Hermitian pairing -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.HermitianMatrix

open SU3Root

variable {A : Type u} [CommRing A] {Idx : Type v} [Fintype Idx] [DecidableEq Idx]
  {c : RingInvolution A}

namespace Form

/-- Multiplication by the actual invertible Gram matrix is a linear equivalence. -/
def gramCoordinates (H : Form c Idx) : (Idx → A) ≃ₗ[A] (Idx → A) :=
  (Matrix.GeneralLinearGroup.toLin H.gram).toLinearEquiv

@[simp] theorem gramCoordinates_apply (H : Form c Idx) (x : Idx → A) :
    H.gramCoordinates x = (H.gram : Matrix Idx Idx A).mulVec x := rfl

/-- The finite-sum pairing agrees with the column-vector matrix convention. -/
theorem pairing_eq_dotProduct (H : Form c Idx) (x y : Idx → A) :
    H.pairing x y =
      dotProduct (fun i => c.bar (x i)) ((H.gram : Matrix Idx Idx A).mulVec y) := by
  simp [pairing, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/-- The linear-first convention used in the split-rank interface. -/
theorem linearFirst_eq_dotProduct (H : Form c Idx) (x y : Idx → A) :
    H.linearFirst x y =
      dotProduct (fun i => c.bar (y i)) ((H.gram : Matrix Idx Idx A).mulVec x) :=
  H.pairing_eq_dotProduct y x

@[simp] theorem pairing_single_left (H : Form c Idx) (i : Idx) (y : Idx → A) :
    H.pairing (Pi.single i 1) y = (H.gram : Matrix Idx Idx A).mulVec y i := by
  simp [pairing, Pi.single_apply, Matrix.mulVec, dotProduct]

/-- Vanishing against every first argument forces the second vector to be zero. -/
theorem eq_zero_of_pairing_right (H : Form c Idx) (y : Idx → A)
    (hy : ∀ x, H.pairing x y = 0) : y = 0 := by
  apply Matrix.mulVec_injective_of_isUnit H.gram.isUnit
  funext i
  simpa using hy (Pi.single i 1)

/-- Hermitian symmetry gives nondegeneracy in the other argument. -/
theorem eq_zero_of_pairing_left (H : Form c Idx) (x : Idx → A)
    (hx : ∀ y, H.pairing x y = 0) : x = 0 := by
  apply H.eq_zero_of_pairing_right x
  intro y
  rw [← H.bar_pairing x y, hx y, map_zero]

theorem sesquilinear_nondegenerate (H : Form c Idx) : H.sesquilinear.Nondegenerate :=
  ⟨H.eq_zero_of_pairing_left, H.eq_zero_of_pairing_right⟩

theorem linearFirst_nondegenerate (H : Form c Idx) : H.linearFirst.Nondegenerate :=
  ⟨H.eq_zero_of_pairing_right, H.eq_zero_of_pairing_left⟩

end Form
end Langlands.GroupScheme.HermitianMatrix
