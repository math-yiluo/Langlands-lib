import Langlands.Representation.RankinSelberg.TwoBlockLowerUnipotentQuotientData
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Rectangle coordinates in the strictly dominant JPSS matrix

The two Weyl-conjugated diagonal blocks give the simultaneous linear change
`(x,y) ↦ (LA⁻¹ x, y LB)`. No positivity is required of either rectangle width.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open GeneralLinear TwoBlockLowerUnipotentQuotient

universe uF

variable {K : Type uF} [Field K]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The lower unipotent multiplier `w_a uA w_a` on the first rectangle. -/
def leftMultiplier (u : lowerBlockUnipotent h K) : GeneralLinear (m 0 + 1) K :=
  weylLong (m 0 + 1) K * (diagonalBlocks h K u 0).val * weylLong (m 0 + 1) K

/-- The lower unipotent multiplier `w_b uB w_b` on the second rectangle. -/
def rightMultiplier (u : lowerBlockUnipotent h K) : GeneralLinear (m 1 + 1) K :=
  weylLong (m 1 + 1) K * (diagonalBlocks h K u 1).val * weylLong (m 1 + 1) K

@[simp] theorem leftMultiplier_apply (u : lowerBlockUnipotent h K)
    (i l : Fin (m 0 + 1)) :
    leftMultiplier h u i l = (diagonalBlocks h K u 0).val i.rev l.rev := by
  exact weylLong_conjugate_entry _ _ _ _ _

@[simp] theorem rightMultiplier_apply (u : lowerBlockUnipotent h K)
    (i l : Fin (m 1 + 1)) :
    rightMultiplier h u i l = (diagonalBlocks h K u 1).val i.rev l.rev := by
  exact weylLong_conjugate_entry _ _ _ _ _

/-- Conjugation preserves the determinant one of the actual first diagonal block. -/
@[simp] theorem det_leftMultiplier (u : lowerBlockUnipotent h K) :
    Matrix.det (leftMultiplier h u).val = 1 := by
  have he := congrArg (fun g : GeneralLinear (m 0 + 1) K => Matrix.det g.val)
    (weylLong_mul_self (m 0 + 1) K)
  change Matrix.det ((weylLong (m 0 + 1) K).val *
    (diagonalBlocks h K u 0).val.val * (weylLong (m 0 + 1) K).val) = 1
  simpa only [Units.val_mul, Matrix.det_mul, unipotent_det, mul_one, Units.val_one, Matrix.det_one]
    using he

/-- Conjugation preserves the determinant one of the actual second diagonal block. -/
@[simp] theorem det_rightMultiplier (u : lowerBlockUnipotent h K) :
    Matrix.det (rightMultiplier h u).val = 1 := by
  have he := congrArg (fun g : GeneralLinear (m 1 + 1) K => Matrix.det g.val)
    (weylLong_mul_self (m 1 + 1) K)
  change Matrix.det ((weylLong (m 1 + 1) K).val *
    (diagonalBlocks h K u 1).val.val * (weylLong (m 1 + 1) K).val) = 1
  simpa only [Units.val_mul, Matrix.det_mul, unipotent_det, mul_one, Units.val_one, Matrix.det_one]
    using he

/-- Both rectangle variables, retaining empty rectangles. -/
abbrev Rectangles (m : Fin 2 → ℕ) (j k : ℕ) (K : Type uF) :=
  Matrix (Fin (m 0 + 1)) (Fin k) K × Matrix (Fin j) (Fin (m 1 + 1)) K

/-- The actual linear change of the two rectangles, with explicit inverse
`(x',y') ↦ (LA x', y' LB⁻¹)`. -/
def rectangleChange (j k : ℕ) (u : lowerBlockUnipotent h K) :
    Rectangles m j k K ≃ₗ[K] Rectangles m j k K where
  toFun p := (((leftMultiplier h u)⁻¹).val * p.1, p.2 * (rightMultiplier h u).val)
  invFun p := ((leftMultiplier h u).val * p.1, p.2 * ((rightMultiplier h u)⁻¹).val)
  left_inv p := by
    dsimp
    congr 1
    · rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    · rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  right_inv p := by
    dsimp
    congr 1
    · rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    · rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Matrix.mul_add, Matrix.add_mul, Prod.mk_add_mk]
  map_smul' z p := by
    change (((leftMultiplier h u)⁻¹).val * (z • p.1),
      (z • p.2) * (rightMultiplier h u).val) =
      (z • (((leftMultiplier h u)⁻¹).val * p.1), z • (p.2 * (rightMultiplier h u).val))
    simp only [Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem rectangleChange_apply (j k : ℕ) (u : lowerBlockUnipotent h K)
    (x : Matrix (Fin (m 0 + 1)) (Fin k) K)
    (y : Matrix (Fin j) (Fin (m 1 + 1)) K) :
    rectangleChange h j k u (x,y) =
      (((leftMultiplier h u)⁻¹).val * x, y * (rightMultiplier h u).val) := rfl

@[simp] theorem rectangleChange_symm_apply (j k : ℕ) (u : lowerBlockUnipotent h K)
    (x : Matrix (Fin (m 0 + 1)) (Fin k) K)
    (y : Matrix (Fin j) (Fin (m 1 + 1)) K) :
    (rectangleChange h j k u).symm (x,y) =
      ((leftMultiplier h u).val * x, y * ((rightMultiplier h u)⁻¹).val) := rfl

section Topology

variable [TopologicalSpace K] [IsTopologicalRing K]

/-- The coordinate change is continuous for every topological field. -/
theorem continuous_rectangleChange (j k : ℕ) (u : lowerBlockUnipotent h K) :
    Continuous (rectangleChange h j k u) := by
  change Continuous (fun p : Rectangles m j k K =>
    (((leftMultiplier h u)⁻¹).val * p.1, p.2 * (rightMultiplier h u).val))
  apply Continuous.prodMk
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro l
    simp only [Matrix.mul_apply]
    fun_prop
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro l
    simp only [Matrix.mul_apply]
    fun_prop

/-- The explicit inverse coordinate change is continuous. -/
theorem continuous_rectangleChange_symm (j k : ℕ) (u : lowerBlockUnipotent h K) :
    Continuous (rectangleChange h j k u).symm := by
  change Continuous (fun p : Rectangles m j k K =>
    ((leftMultiplier h u).val * p.1, p.2 * ((rightMultiplier h u)⁻¹).val))
  apply Continuous.prodMk
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro l
    simp only [Matrix.mul_apply]
    fun_prop
  · apply continuous_pi
    intro i
    apply continuous_pi
    intro l
    simp only [Matrix.mul_apply]
    fun_prop

end Topology

/-- Continuity for the canonical topology on an arbitrary algebraic p-adic field. -/
theorem continuous_rectangleChange_canonical {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (j k : ℕ) (u : lowerBlockUnipotent h F.Carrier) :
    let := F.canonicalTopologicalData.topology
    Continuous (rectangleChange h j k u) ∧ Continuous (rectangleChange h j k u).symm := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  exact ⟨continuous_rectangleChange h j k u, continuous_rectangleChange_symm h j k u⟩

end Langlands.RankinSelberg.TwoBlockDominantRectangular
