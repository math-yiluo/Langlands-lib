import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonAffineSlice

/-! Complementary anti-triangular affine slices for the JPSS rectangular identity. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped BigOperators

namespace Langlands.HarmonicAnalysis

universe uK

/-- Free coordinates strictly beyond the antidiagonal in size `n + 1`. -/
def adjacentRankRightColumns (n : ℕ) (i : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun j => n < i.val + j.val

variable {K : Type uK} [Field K]

/-- The antidiagonal with all entries one. -/
def adjacentRankAntidiagonal (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  fun i j => if i.val + j.val = n then 1 else 0

/-- The negative antidiagonal shifted one column to the right. -/
def adjacentRankShiftedAntidiagonal (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  fun i j => if i.val + j.val = n + 1 then -1 else 0

/-- Pairing with the antidiagonal, with no signs suppressed. -/
def adjacentRankAntiTrace (n : ℕ) (X : Matrix (Fin (n + 1)) (Fin (n + 1)) K) : K :=
  ∑ i, X i i.rev

/-- Pairing with the antidiagonal shifted one column to the right. -/
def adjacentRankShiftedAntiTrace (n : ℕ)
    (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) K) : K :=
  ∑ i : Fin n, Y i.succ i.rev.succ

variable [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [T2Space K]

/-- The affine slice `w*u`, with coordinate-product measure on its free entries. -/
def adjacentRankRightSliceMeasure (ν : AdditiveHaarMeasure K) (n : ℕ) :
    Measure (Matrix (Fin (n + 1)) (Fin (n + 1)) K) :=
  rectangularCoordinateSliceMeasure ν (adjacentRankRightColumns n)
    (adjacentRankAntidiagonal n)

/-- The complementary affine slice, including its whole free first column. -/
def adjacentRankLeftSliceMeasure (ν : AdditiveHaarMeasure K) (n : ℕ) :
    Measure (Matrix (Fin (n + 1)) (Fin (n + 1)) K) :=
  rectangularCoordinateSliceMeasure ν (fun i => (adjacentRankRightColumns n i)ᶜ)
    (adjacentRankShiftedAntidiagonal n)

omit [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K]
  [BorelSpace K] [T2Space K] in
private theorem adjacentRank_mask_shift (n : ℕ) :
    rectangularCoordinateMask (adjacentRankRightColumns n)
      (-(adjacentRankShiftedAntidiagonal n : Matrix _ _ K)) =
      -adjacentRankShiftedAntidiagonal n := by
  ext i j
  by_cases h : i.val + j.val = n + 1
  · have hm : j ∈ adjacentRankRightColumns n i := by
      simp only [adjacentRankRightColumns, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    simp [rectangularCoordinateMask, coordinateMask, hm]
  · simp [rectangularCoordinateMask, coordinateMask, adjacentRankShiftedAntidiagonal, h]

omit [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K]
  [BorelSpace K] [T2Space K] in
private theorem adjacentRank_mask_anti (n : ℕ) :
    rectangularCoordinateMask (fun i => (adjacentRankRightColumns n i)ᶜ)
      (adjacentRankAntidiagonal n : Matrix _ _ K) = adjacentRankAntidiagonal n := by
  ext i j
  by_cases h : i.val + j.val = n
  · have hm : j ∈ (adjacentRankRightColumns n i)ᶜ := by
      simp only [Finset.mem_compl, adjacentRankRightColumns, Finset.mem_filter,
        Finset.mem_univ, true_and]
      omega
    simp [rectangularCoordinateMask, coordinateMask, hm]
  · simp [rectangularCoordinateMask, coordinateMask, adjacentRankAntidiagonal, h]

omit [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K]
  [BorelSpace K] [T2Space K] in
private theorem adjacentRank_pairing_anti (n : ℕ)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    rectangularPairing X (adjacentRankAntidiagonal n) = adjacentRankAntiTrace n X := by
  unfold rectangularPairing adjacentRankAntiTrace
  apply Finset.sum_congr rfl
  intro i _
  have hi := i.isLt
  have hv : i.val + i.rev.val = n := by simp only [Fin.val_rev]; omega
  rw [Finset.sum_eq_single i.rev]
  · change X i i.rev * (if i.val + i.rev.val = n then 1 else 0) = _
    rw [ite_eq_left hv, mul_one]
  · intro j _ hj
    have hne : i.val + j.val ≠ n := by
      intro h
      apply hj
      apply Fin.ext
      simp only [Fin.val_rev]
      omega
    change X i j * (if i.val + j.val = n then 1 else 0) = 0
    rw [ite_eq_right hne, mul_zero]
  · simp

omit [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K]
  [BorelSpace K] [T2Space K] in
private theorem adjacentRank_pairing_shift (n : ℕ)
    (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    rectangularPairing Y (-adjacentRankShiftedAntidiagonal n) =
      adjacentRankShiftedAntiTrace n Y := by
  have hr (i : Fin n) :
      (∑ j, Y i.succ j * (-adjacentRankShiftedAntidiagonal n) i.succ j) =
        Y i.succ i.rev.succ := by
    have hi := i.isLt
    have hv : i.succ.val + i.rev.succ.val = n + 1 := by
      simp only [Fin.val_succ, Fin.val_rev]
      omega
    rw [Finset.sum_eq_single i.rev.succ]
    · change Y i.succ i.rev.succ *
        -(if i.succ.val + i.rev.succ.val = n + 1 then -1 else 0) = _
      rw [ite_eq_left hv]
      simp
    · intro j _ hj
      have hne : i.succ.val + j.val ≠ n + 1 := by
        intro h
        apply hj
        apply Fin.ext
        simp only [Fin.val_succ, Fin.val_rev] at *
        omega
      change Y i.succ j * -(if i.succ.val + j.val = n + 1 then -1 else 0) = 0
      rw [ite_eq_right hne]
      simp
    · simp
  have hz : (∑ j, Y 0 j * (-adjacentRankShiftedAntidiagonal n) 0 j) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hne : (0 : Fin (n + 1)).val + j.val ≠ n + 1 := by
      have hj := j.isLt
      simp only [Fin.val_zero]
      omega
    change Y 0 j * -(if (0 : Fin (n + 1)).val + j.val = n + 1 then -1 else 0) = 0
    rw [ite_eq_right hne]
    simp
  unfold rectangularPairing
  rw [Fin.sum_univ_succ, hz, zero_add]
  simp only [hr, adjacentRankShiftedAntiTrace]

variable [LocallyCompactSpace K] [TotallyDisconnectedSpace K]

/-- Complementary anti-triangular Fourier inversion with the exact positive
phases that occur after expanding the JPSS final-column transform. -/
theorem adjacentRankAffine_fourier_duality (ψ : UnitaryAdditiveCharacter K)
    (ν : AdditiveHaarMeasure K) [SigmaFinite ν.measure] (hsd : IsSelfDual ψ ν)
    (n : ℕ) (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) K)) :
    Integrable (fun Y => ψ.complex (adjacentRankShiftedAntiTrace n Y) *
      rectangularFourierIntegral ψ ν Φ Y) (adjacentRankRightSliceMeasure ν n) ∧
    Integrable (fun X => ψ.complex (adjacentRankAntiTrace n X) * Φ X)
      (adjacentRankLeftSliceMeasure ν n) ∧
    (∫ Y, ψ.complex (adjacentRankShiftedAntiTrace n Y) *
      rectangularFourierIntegral ψ ν Φ Y ∂adjacentRankRightSliceMeasure ν n) =
      ∫ X, ψ.complex (adjacentRankAntiTrace n X) * Φ X
        ∂adjacentRankLeftSliceMeasure ν n := by
  simpa only [adjacentRank_mask_shift, adjacentRank_mask_anti,
    adjacentRank_pairing_shift, adjacentRank_pairing_anti,
    adjacentRankRightSliceMeasure, adjacentRankLeftSliceMeasure] using
    rectangularCoordinateSlice_fourier_duality ψ ν hsd Φ (adjacentRankRightColumns n)
      (adjacentRankShiftedAntidiagonal n) (adjacentRankAntidiagonal n)

end Langlands.HarmonicAnalysis
