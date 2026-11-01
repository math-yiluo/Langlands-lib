import Langlands.Representation.RankinSelberg.TwoBlockDominantRectangularData

/-! # Residual upper unipotent and its character for JPSS Section 4.10 -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open GeneralLinear TwoBlockLowerUnipotentQuotient Whittaker HarmonicAnalysis

universe uF

variable {K : Type uF} [Field K]
variable {t r j k : ℕ} {m : Fin 2 → ℕ}
variable (h : ∑ i, (m i+1) = t+1) (hr : r=t+(j+k+1))
variable (u : lowerBlockUnipotent h K)
variable (x : Matrix (Fin (m 0+1)) (Fin k) K)
variable (y : Matrix (Fin j) (Fin (m 1+1)) K)

/-- The residual in the full five-block order; its nonzero extra blocks all lie at least
 two positions below the diagonal because the middle singleton separates the rectangles. -/
def residualFive : Matrix (Coordinates (m 0+1) j k (m 1+1))
    (Coordinates (m 0+1) j k (m 1+1)) K
  | .inl i, .inl l => leftMultiplier h u i l
  | .inr (.inl (.inl i)), .inr (.inl (.inl l)) => (1 : Matrix (Fin k) (Fin k) K) i l
  | .inr (.inl (.inr (.inl i))), .inr (.inl (.inr (.inl l))) =>
      (1 : Matrix (Fin 1) (Fin 1) K) i l
  | .inr (.inl (.inr (.inr i))), .inr (.inl (.inr (.inr l))) =>
      (1 : Matrix (Fin j) (Fin j) K) i l
  | .inr (.inr i), .inr (.inr l) => rightMultiplier h u i l
  | .inr (.inl (.inr (.inr i))), .inl l => (y * crossMultiplier h u) i l
  | .inr (.inl (.inr (.inr i))), .inr (.inl (.inl l)) =>
      -((y * crossMultiplier h u) * (((leftMultiplier h u)⁻¹).val * x)) i l
  | .inr (.inr i), .inl l => crossMultiplier h u i l
  | .inr (.inr i), .inr (.inl (.inl l)) =>
      -(crossMultiplier h u * (((leftMultiplier h u)⁻¹).val * x)) i l
  | _, _ => 0

/-- Evaluation of the actual residual in all five blocks. -/
theorem residualMatrix_five_entry (i l : Coordinates (m 0+1) j k (m 1+1)) :
    residualMatrix h hr u x y (coordinates h hr i) (coordinates h hr l) =
      residualFive h u x y i l := by
  rw [residualMatrix_entry]
  rcases i with i | ((i | (i | i)) | i) <;>
    rcases l with l | ((l | (l | l)) | l) <;>
    simp [residualFive, BlockAlgebra.three, padX, padY, Matrix.fromRows_mul,
      Matrix.mul_fromCols, Matrix.sub_apply, Matrix.one_apply, Matrix.mul_assoc]

/-- The residual has diagonal entries one, including the three middle pieces. -/
theorem residualFive_diag (i : Coordinates (m 0+1) j k (m 1+1)) :
    residualFive h u x y i i = 1 := by
  rcases i with i | ((i | (i | i)) | i) <;>
    simp [residualFive, leftMultiplier_apply, rightMultiplier_apply]

/-- All entries above the diagonal vanish in the displayed block order. -/
theorem residualFive_above (i l : Coordinates (m 0+1) j k (m 1+1))
    (hil : position i < position l) : residualFive h u x y i l = 0 := by
  rcases i with i | ((i | (i | i)) | i) <;>
    rcases l with l | ((l | (l | l)) | l) <;>
    simp only [position] at hil <;> simp only [residualFive]
  all_goals first
    | rfl
    | omega
    | (apply Matrix.one_apply_ne; intro he; subst l; omega)
    | (rw [leftMultiplier_apply]; exact UpperUnipotent.entry_eq_zero _
        (Fin.rev_lt_rev.mpr (show i < l from hil)))
    | (rw [rightMultiplier_apply]; apply UpperUnipotent.entry_eq_zero _;
        apply Fin.rev_lt_rev.mpr; exact (show i < l by omega))

/-- A first-subdiagonal entry outside the two end blocks is zero. The singleton
forces each extra rectangle product to be at least two positions below the diagonal. -/
private theorem residualFive_middle_subdiagonal
    (i l : Coordinates (m 0+1) j k (m 1+1))
    (hadj : position i = position l + 1)
    (hl : m 0 ≤ position l) (hi : position i ≤ m 0+1+(j+k+1)) :
    residualFive h u x y i l = 0 := by
  rcases i with i | ((i | (i | i)) | i) <;>
    rcases l with l | ((l | (l | l)) | l) <;>
    simp only [position] at hadj hl hi <;> simp only [residualFive]
  all_goals first
    | rfl
    | omega
    | (apply Matrix.one_apply_ne; intro he; subst l; omega)

/-- The standard-coordinate middle and boundary subdiagonal entries vanish. -/
private theorem residualMatrix_middle_subdiagonal (i : Fin r)
    (hl : m 0 ≤ i.val) (hi : i.val ≤ m 0+(j+k+1)) :
    residualMatrix h hr u x y i.succ i.castSucc = 0 := by
  obtain ⟨i', hi'⟩ := (coordinates h hr).surjective i.succ
  obtain ⟨l', hl'⟩ := (coordinates h hr).surjective i.castSucc
  have hiv : position i' = i.val+1 := by
    simpa only [coordinates_val, Fin.val_succ] using congrArg Fin.val hi'
  have hlv : position l' = i.val := by
    simpa only [coordinates_val, Fin.val_castSucc] using congrArg Fin.val hl'
  rw [← hi', ← hl', residualMatrix_five_entry]
  apply residualFive_middle_subdiagonal
  · omega
  · omega
  · omega

/-- Only the first subdiagonals of the two end blocks contribute to the residual. -/
theorem residualMatrix_subdiagonal_sum :
    (∑ i : Fin r, residualMatrix h hr u x y i.succ i.castSucc) =
      (∑ i : Fin (m 0), leftMultiplier h u i.succ i.castSucc) +
      ∑ i : Fin (m 1), rightMultiplier h u i.succ i.castSucc := by
  have htotal := TwoBlockJacquet.blockRanks_add h
  obtain rfl : r = (m 0 + (j+k+1+1)) + m 1 := by omega
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  have hA (i : Fin (m 0)) :
      residualMatrix h hr u x y
        ((i.castAdd (j+k+1+1)).castAdd (m 1)).succ
        ((i.castAdd (j+k+1+1)).castAdd (m 1)).castSucc =
        leftMultiplier h u i.succ i.castSucc := by
    have e1 : ((i.castAdd (j+k+1+1)).castAdd (m 1)).succ =
        coordinates h hr (.inl i.succ) := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_castAdd, coordinates_val, position]
    have e2 : ((i.castAdd (j+k+1+1)).castAdd (m 1)).castSucc =
        coordinates h hr (.inl i.castSucc) := by
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_castAdd, coordinates_val, position]
    rw [e1, e2, residualMatrix_five_entry]
    rfl
  have hB (i : Fin (m 1)) :
      residualMatrix h hr u x y (i.natAdd (m 0+(j+k+1+1))).succ
        (i.natAdd (m 0+(j+k+1+1))).castSucc =
        rightMultiplier h u i.succ i.castSucc := by
    have e1 : (i.natAdd (m 0+(j+k+1+1))).succ =
        coordinates h hr (.inr (.inr i.succ)) := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_natAdd, coordinates_val, position]
      omega
    have e2 : (i.natAdd (m 0+(j+k+1+1))).castSucc =
        coordinates h hr (.inr (.inr i.castSucc)) := by
      apply Fin.ext
      simp only [Fin.val_castSucc, Fin.val_natAdd, coordinates_val, position]
      omega
    rw [e1, e2, residualMatrix_five_entry]
    rfl
  have hC (i : Fin (j+k+1+1)) :
      residualMatrix h hr u x y ((i.natAdd (m 0)).castAdd (m 1)).succ
        ((i.natAdd (m 0)).castAdd (m 1)).castSucc = 0 := by
    apply residualMatrix_middle_subdiagonal
    · simp only [Fin.val_castAdd, Fin.val_natAdd]; omega
    · simp only [Fin.val_castAdd, Fin.val_natAdd]; omega
  simp only [hA, hB, hC, Finset.sum_const_zero, add_zero]

/-- The constructed long-Weyl conjugate is an actual standard upper-unipotent element. -/
def residualUnipotent : upperUnipotent (r+1) K := by
  refine ⟨weylLong (r+1) K * residualMatrix h hr u x y * weylLong (r+1) K, ?_⟩
  constructor
  · intro i l hli
    rw [weylLong_conjugate_entry]
    obtain ⟨i', hi⟩ := (coordinates h hr).surjective i.rev
    obtain ⟨l', hl⟩ := (coordinates h hr).surjective l.rev
    rw [← hi, ← hl, residualMatrix_five_entry]
    apply residualFive_above
    have hh : i.rev < l.rev := Fin.rev_lt_rev.mpr hli
    rw [← hi, ← hl, Fin.lt_def, coordinates_val, coordinates_val] at hh
    exact hh
  · intro i
    rw [weylLong_conjugate_entry]
    obtain ⟨i', hi⟩ := (coordinates h hr).surjective i.rev
    rw [← hi, residualMatrix_five_entry, residualFive_diag]

/-- The value of the residual upper unipotent is the specified Weyl conjugate. -/
@[simp] theorem residualUnipotent_val :
    (residualUnipotent h hr u x y).val =
      weylLong (r+1) K * residualMatrix h hr u x y * weylLong (r+1) K := rfl

/-- Reversing all indices turns the residual's two lower subdiagonals back into
precisely the two original block superdiagonals. -/
theorem residualUnipotent_superdiagonal_sum :
    (∑ i : Fin r, (residualUnipotent h hr u x y).val i.castSucc i.succ) =
      (∑ i : Fin (m 0), (diagonalBlocks h K u 0).val i.castSucc i.succ) +
      ∑ i : Fin (m 1), (diagonalBlocks h K u 1).val i.castSucc i.succ := by
  simp only [residualUnipotent_val, weylLong_conjugate_entry,
    Fin.rev_castSucc, Fin.rev_succ]
  have hs : (∑ i : Fin r, residualMatrix h hr u x y i.rev.succ i.rev.castSucc) =
      ∑ i : Fin r, residualMatrix h hr u x y i.succ i.castSucc :=
    Equiv.sum_comp Fin.revPerm
      (fun i : Fin r => residualMatrix h hr u x y i.succ i.castSucc)
  rw [hs, residualMatrix_subdiagonal_sum]
  simp only [leftMultiplier_apply, rightMultiplier_apply, Fin.rev_succ, Fin.rev_castSucc]
  congr 1
  · exact Equiv.sum_comp Fin.revPerm
      (fun i : Fin (m 0) => (diagonalBlocks h K u 0).val i.castSucc i.succ)
  · exact Equiv.sum_comp Fin.revPerm
      (fun i : Fin (m 1) => (diagonalBlocks h K u 1).val i.castSucc i.succ)

/-- The residual has exactly the positive product character of the two actual
upper-unipotent diagonal blocks. No rectangle dimension is assumed positive. -/
theorem residualUnipotent_character [TopologicalSpace K]
    (ψ : UnitaryAdditiveCharacter K) :
    standardCharacter ψ r (residualUnipotent h hr u x y) =
      standardCharacter ψ (m 0) (diagonalBlocks h K u 0) *
        standardCharacter ψ (m 1) (diagonalBlocks h K u 1) := by
  apply Units.ext
  simp only [Units.val_mul, standardCharacter_apply, residualUnipotent_superdiagonal_sum,
    AddChar.map_add_eq_mul]

end Langlands.RankinSelberg.TwoBlockDominantRectangular
