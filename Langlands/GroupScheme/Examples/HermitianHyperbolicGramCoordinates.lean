import Langlands.GroupScheme.Examples.HermitianHyperbolicDecomposition
import Langlands.GroupScheme.Examples.HermitianHyperbolicDiagonal
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Actual matrix coordinates for several hyperbolic planes -/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

namespace MultiHyperbolic

variable {A : Type u} [CommRing A] {α : Type v} {β : Type w}

/-- Split a function on the three blocks into its three coordinate families. -/
def productCoordinates : (Index α β → A) ≃ₗ[A] (α → A) × ((β → A) × (α → A)) :=
  (LinearEquiv.sumArrowLequivProdArrow α (β ⊕ α) A A).trans
    ((LinearEquiv.refl A (α → A)).prodCongr
      (LinearEquiv.sumArrowLequivProdArrow β α A A))

@[simp] theorem productCoordinates_apply (z : Index α β → A) :
    productCoordinates z =
      (fun i => z (Sum.inl i), (fun i => z (Sum.inr (Sum.inl i)),
        fun i => z (Sum.inr (Sum.inr i)))) := rfl

@[simp] theorem productCoordinates_single_top [DecidableEq α] [DecidableEq β] (j : α) :
    productCoordinates (Pi.single (Sum.inl j) (1 : A) : Index α β → A) =
      (Pi.single j 1, (0, 0)) := by
  ext i <;> simp [Pi.single_apply]

@[simp] theorem productCoordinates_single_middle [DecidableEq α] [DecidableEq β] (j : β) :
    productCoordinates (Pi.single (Sum.inr (Sum.inl j)) (1 : A) : Index α β → A) =
      (0, (Pi.single j 1, 0)) := by
  ext i <;> simp [Pi.single_apply]

@[simp] theorem productCoordinates_single_bottom [DecidableEq α] [DecidableEq β] (j : α) :
    productCoordinates (Pi.single (Sum.inr (Sum.inr j)) (1 : A) : Index α β → A) =
      (0, (0, Pi.single j 1)) := by
  ext i <;> simp [Pi.single_apply]

variable {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- The actual invertible matrix of an automorphism of function coordinates. -/
def coordinateMatrix (e : (ι → A) ≃ₗ[A] (ι → A)) :
    Matrix.GeneralLinearGroup ι A :=
  Units.map LinearMap.toMatrixAlgEquiv'.toMonoidHom
    (LinearMap.GeneralLinearGroup.ofLinearEquiv e)

@[simp] theorem coordinateMatrix_apply
    (e : (ι → A) ≃ₗ[A] (ι → A)) (i j : ι) :
    (coordinateMatrix e : Matrix ι ι A) i j = e (Pi.single j 1) i := rfl

/-- Each entry of the Gram congruence is the original full pairing of the
corresponding coordinate vectors. -/
theorem coordinateMatrix_congruence_apply (c : RingInvolution A)
    (J : Matrix ι ι A) (e : (ι → A) ≃ₗ[A] (ι → A)) (i j : ι) :
    (((coordinateMatrix e : Matrix ι ι A).map c.bar).transpose * J *
        (coordinateMatrix e : Matrix ι ι A)) i j =
      dotProduct (fun k => c.bar (e (Pi.single i 1) k))
        (J.mulVec (e (Pi.single j 1))) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    coordinateMatrix_apply, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

end MultiHyperbolic

namespace HyperbolicDecomposition

variable {L : Type u} [Field L] {c : RingInvolution L}
  {V : Type v} [AddCommGroup V] [Module L V]
  {h : V →ₗ[L] V →ₛₗ[c.bar.toRingHom] L} {r : ℕ}
  (d : HyperbolicDecomposition h r)

/-- The same actual decomposition in single function coordinates. -/
def functionCoordinates :
    V ≃ₗ[L] (MultiHyperbolic.Index (Fin r) (Fin d.middleDimension) → L) :=
  d.coordinates.trans MultiHyperbolic.productCoordinates.symm

/-- The middle block is evaluated from the original full pairing. -/
def middleGram : Matrix (Fin d.middleDimension) (Fin d.middleDimension) L :=
  fun i j => h
    (d.coordinates.symm (0, (Pi.single j 1, 0)))
    (d.coordinates.symm (0, (Pi.single i 1, 0)))

theorem middlePairing_zero_left (z : Fin d.middleDimension → L) :
    d.middlePairing 0 z = 0 := by
  have hd := d.pairing_eq 0 (d.coordinates.symm (0, (z, 0)))
  rw [h.map_zero₂] at hd
  simpa using hd.symm

theorem middlePairing_zero_right (z : Fin d.middleDimension → L) :
    d.middlePairing z 0 = 0 := by
  have hd := d.pairing_eq (d.coordinates.symm (0, (z, 0))) 0
  rw [(h _).map_zero] at hd
  simpa using hd.symm

@[simp] theorem middleGram_apply (i j : Fin d.middleDimension) :
    d.middleGram i j = d.middlePairing (Pi.single j 1) (Pi.single i 1) := by
  unfold middleGram
  rw [d.pairing_eq]
  simp

/-- On standard coordinate vectors the transported pairing has exactly the
identity cross blocks and the actual remaining middle block. -/
theorem functionCoordinates_basis_pairing
    (i j : MultiHyperbolic.Index (Fin r) (Fin d.middleDimension)) :
    h (d.functionCoordinates.symm (Pi.single j 1))
      (d.functionCoordinates.symm (Pi.single i 1)) =
        MultiHyperbolic.gram d.middleGram i j := by
  rw [d.pairing_eq]
  have hc (z : MultiHyperbolic.Index (Fin r) (Fin d.middleDimension) → L) :
      d.coordinates (d.functionCoordinates.symm z) = MultiHyperbolic.productCoordinates z := by
    simp [functionCoordinates]
  simp only [hc]
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [MultiHyperbolic.gram, Pi.single_apply]
  all_goals first
    | exact d.middlePairing_zero_left _
    | exact d.middlePairing_zero_right _
    | congr 1 <;> funext k <;> simp [Pi.single_apply]

variable {ι : Type w} [Fintype ι] [DecidableEq ι]
  {h : (ι → L) →ₗ[L] (ι → L) →ₛₗ[c.bar.toRingHom] L}
  (d : HyperbolicDecomposition h r)

/-- There are exactly enough indices for the displayed hyperbolic blocks. -/
def indexEquiv : ι ≃ MultiHyperbolic.Index (Fin r) (Fin d.middleDimension) :=
  Fintype.equivOfCardEq (by
    have hd := d.finrank_eq
    simp only [Module.finrank_fintype_fun_eq_card] at hd
    simp only [MultiHyperbolic.Index, Fintype.card_sum, Fintype.card_fin]
    omega)

/-- From reindexed block coordinates back to the original coordinates. -/
def basisCoordinates : (ι → L) ≃ₗ[L] (ι → L) :=
  (LinearEquiv.piCongrLeft' L (fun _ => L) d.indexEquiv).trans d.functionCoordinates.symm

@[simp] theorem basisCoordinates_single (j : ι) :
    d.basisCoordinates (Pi.single j 1) =
      d.functionCoordinates.symm (Pi.single (d.indexEquiv j) 1) := by
  simp only [basisCoordinates, LinearEquiv.trans_apply]
  apply congrArg d.functionCoordinates.symm
  ext i
  simp [Pi.single_apply, Equiv.symm_apply_eq]

/-- The decomposition supplies an actual invertible Gram congruence. -/
theorem gram_congruence (J : Matrix ι ι L)
    (hJ : ∀ z w, h z w = dotProduct (fun i => c.bar (w i)) (J.mulVec z)) :
    ((MultiHyperbolic.coordinateMatrix d.basisCoordinates : Matrix ι ι L).map
        c.bar).transpose * J *
        (MultiHyperbolic.coordinateMatrix d.basisCoordinates : Matrix ι ι L) =
      (MultiHyperbolic.gram d.middleGram).submatrix d.indexEquiv d.indexEquiv := by
  ext i j
  rw [MultiHyperbolic.coordinateMatrix_congruence_apply, ← hJ,
    d.basisCoordinates_single, d.basisCoordinates_single]
  exact d.functionCoordinates_basis_pairing _ _

end HyperbolicDecomposition

end Langlands.GroupScheme.HermitianRoot
