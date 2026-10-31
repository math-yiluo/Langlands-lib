import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonAffineSlice

/-! The explicit shifted-triangular affine Fourier identity. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped BigOperators

namespace Langlands.HarmonicAnalysis

universe uK

/-- The free entries of the shifted lower-triangular slice: the last entry
of the first column and the entries on or below the trailing diagonal. -/
def shiftedLowerSliceColumns (n : ℕ) (i : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun j => (j = 0 ∧ i = Fin.last n) ∨ (0 < j ∧ j ≤ i)

variable {K : Type uK} [Field K]

/-- The diagonal matrix with first entry zero and all remaining entries one. -/
def trailingIdentity (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  fun i j => if i = j ∧ i ≠ 0 then 1 else 0

/-- The matrix with `-1` on the superdiagonal and zero elsewhere. -/
def negativeSuperdiagonal (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  fun i j => if i.val + 1 = j.val then -1 else 0

variable [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [T2Space K]

/-- The actual product measure on the shifted lower-triangular affine slice.
Every non-free entry is fixed at the negative superdiagonal. -/
def shiftedLowerSliceMeasure (ν : AdditiveHaarMeasure K) (n : ℕ) :
    Measure (Matrix (Fin (n + 1)) (Fin (n + 1)) K) :=
  rectangularCoordinateSliceMeasure ν (shiftedLowerSliceColumns n)
    (negativeSuperdiagonal n)

/-- The complementary upper affine slice, with trailing diagonal equal to one.
Its first column is free except for the final entry, which is zero. -/
def upperFirstColumnSliceMeasure (ν : AdditiveHaarMeasure K) (n : ℕ) :
    Measure (Matrix (Fin (n + 1)) (Fin (n + 1)) K) :=
  rectangularCoordinateSliceMeasure ν (fun i => (shiftedLowerSliceColumns n i)ᶜ)
    (trailingIdentity n)

omit [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K]
  [BorelSpace K] [T2Space K] in
private theorem mask_negative_trailingIdentity (n : ℕ) :
    rectangularCoordinateMask (shiftedLowerSliceColumns n)
      (-(trailingIdentity n : Matrix _ _ K)) = -trailingIdentity n := by
  ext i j
  by_cases h : i = j ∧ i ≠ 0
  · have hj : 0 < j := h.1 ▸ Fin.pos_of_ne_zero h.2
    have hm : j ∈ shiftedLowerSliceColumns n i := by
      simp only [shiftedLowerSliceColumns, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inr ⟨hj, h.1.symm.le⟩
    simp [rectangularCoordinateMask, coordinateMask, hm]
  · simp [rectangularCoordinateMask, coordinateMask, trailingIdentity, h]

omit [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K]
  [BorelSpace K] [T2Space K] in
private theorem mask_complement_negativeSuperdiagonal (n : ℕ) :
    rectangularCoordinateMask (fun i => (shiftedLowerSliceColumns n i)ᶜ)
      (negativeSuperdiagonal n : Matrix _ _ K) = negativeSuperdiagonal n := by
  ext i j
  by_cases h : i.val + 1 = j.val
  · have hj : j ≠ 0 := by
      intro hj
      simp only [hj, Fin.val_zero] at h
      omega
    have hji : ¬ j ≤ i := by
      change ¬ j.val ≤ i.val
      omega
    have hm : j ∈ (shiftedLowerSliceColumns n i)ᶜ := by
      apply Finset.mem_compl.mpr
      intro hm
      obtain ⟨_, (⟨hz, _⟩ | ⟨_, hle⟩)⟩ := Finset.mem_filter.mp hm
      · exact hj hz
      · exact hji hle
    simp [rectangularCoordinateMask, coordinateMask, hm]
  · simp [rectangularCoordinateMask, coordinateMask, negativeSuperdiagonal, h]

omit [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K]
  [BorelSpace K] [T2Space K] in
private theorem pairing_negative_trailingIdentity (n : ℕ)
    (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    rectangularPairing Y (-trailingIdentity n) = -∑ i : Fin n, Y i.succ i.succ := by
  have hr (i : Fin (n + 1)) :
      (∑ j, Y i j * (-trailingIdentity n) i j) = if i = 0 then 0 else -Y i i := by
    by_cases hi : i = 0
    · subst i
      simp [trailingIdentity]
    · rw [Finset.sum_eq_single i]
      · simp [trailingIdentity, hi]
      · intro j _ hj
        simp [trailingIdentity, Ne.symm hj]
      · simp
  unfold rectangularPairing
  simp_rw [hr]
  rw [Fin.sum_univ_succ]
  simp [Finset.sum_neg_distrib]

omit [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K]
  [BorelSpace K] [T2Space K] in
private theorem pairing_negativeSuperdiagonal (n : ℕ)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    rectangularPairing X (negativeSuperdiagonal n) =
      -∑ i : Fin n, X i.castSucc i.succ := by
  have hr (i : Fin n) :
      (∑ j, X i.castSucc j * negativeSuperdiagonal n i.castSucc j) =
        -X i.castSucc i.succ := by
    rw [Finset.sum_eq_single i.succ]
    · simp [negativeSuperdiagonal]
    · intro j _ hj
      have hne : i.val + 1 ≠ j.val := by
        intro h
        exact hj (Fin.ext h.symm)
      simp [negativeSuperdiagonal, hne]
    · simp
  have hl : (∑ j, X (Fin.last n) j * negativeSuperdiagonal n (Fin.last n) j) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hne : n + 1 ≠ j.val := by omega
    simp [negativeSuperdiagonal, hne]
  unfold rectangularPairing
  rw [Fin.sum_univ_castSucc, hl, add_zero]
  simp_rw [hr]
  exact Finset.sum_neg_distrib (fun i : Fin n => X i.castSucc i.succ)

variable [LocallyCompactSpace K] [TotallyDisconnectedSpace K]

/-- The shifted lower-triangular Fourier integral equals the complementary
upper affine integral. Both are absolutely convergent with the same supplied
self-dual scalar Haar measure and the explicit negative character phases. -/
theorem shiftedTriangular_fourier_duality (ψ : UnitaryAdditiveCharacter K)
    (ν : AdditiveHaarMeasure K) [SigmaFinite ν.measure] (hsd : IsSelfDual ψ ν)
    (n : ℕ) (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) K)) :
    Integrable (fun Y => ψ.complex (-∑ i : Fin n, Y i.succ i.succ) *
      rectangularFourierIntegral ψ ν Φ Y) (shiftedLowerSliceMeasure ν n) ∧
    Integrable (fun X => ψ.complex (-∑ i : Fin n, X i.castSucc i.succ) * Φ X)
      (upperFirstColumnSliceMeasure ν n) ∧
    (∫ Y, ψ.complex (-∑ i : Fin n, Y i.succ i.succ) *
      rectangularFourierIntegral ψ ν Φ Y ∂shiftedLowerSliceMeasure ν n) =
      ∫ X, ψ.complex (-∑ i : Fin n, X i.castSucc i.succ) * Φ X
        ∂upperFirstColumnSliceMeasure ν n := by
  simpa only [mask_negative_trailingIdentity, mask_complement_negativeSuperdiagonal,
    pairing_negative_trailingIdentity, pairing_negativeSuperdiagonal,
    shiftedLowerSliceMeasure, upperFirstColumnSliceMeasure] using
    rectangularCoordinateSlice_fourier_duality ψ ν hsd Φ
      (shiftedLowerSliceColumns n) (trailingIdentity n) (negativeSuperdiagonal n)

end Langlands.HarmonicAnalysis
