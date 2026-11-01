import Langlands.HarmonicAnalysis.AdjacentRankUnipotentFourierStatement
import Langlands.Group.GL.UpperUnipotentEntryCoordinates

/-! Compact support and convergence on the actual rectangular unipotent slices. -/

noncomputable section

namespace Langlands.HarmonicAnalysis

open MeasureTheory Topology GeneralLinear RankinSelberg Whittaker

universe uK

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [T2Space K] {n : ℕ}

/-- The rectangular affine slice of the actual upper-unipotent group is a
closed embedding, with arbitrary invertible left factor and fixed final column. -/
theorem isClosedEmbedding_rectangularUnipotentSlice
    (g : GeneralLinear n K) (y : Fin n → K) :
    IsClosedEmbedding (fun u : upperUnipotent n K =>
      rectangularJoin (g.val * u.val.val) y) := by
  let e := upperEntryCoordinates n (K := K)
  let π : Matrix (Fin n) (Fin (n + 1)) K → upperUnipotent n K := fun m =>
    e.symm (fun ij => ((g⁻¹).val * rectangularFirstColumns m) ij.1.1 ij.1.2)
  have hc : Continuous (fun u : upperUnipotent n K => u.val.val) :=
    Units.continuous_val.comp continuous_subtype_val
  have hs : Continuous (fun u : upperUnipotent n K =>
      rectangularJoin (g.val * u.val.val) y) :=
    continuous_rectangularJoin.comp
      ((continuous_const.matrix_mul hc).prodMk continuous_const)
  have hπ : Continuous π := by
    apply e.symm.continuous.comp
    exact continuous_pi fun ij =>
      (continuous_const.matrix_mul continuous_rectangularFirstColumns).matrix_elem
        ij.1.1 ij.1.2
  have hleft : Function.LeftInverse π (fun u : upperUnipotent n K =>
      rectangularJoin (g.val * u.val.val) y) := by
    intro u
    apply e.injective
    change e (e.symm _) = e u
    rw [e.apply_symm_apply]
    rw [rectangularFirstColumns_join, ← Matrix.mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mul]
    ext ij
    exact (upperEntryCoordinates_apply u ij).symm
  exact hleft.isClosedEmbedding hπ hs

/-- Restriction of a rectangular Schwartz function to an actual unipotent
slice retains compact support. -/
theorem rectangularUnipotentSlice_hasCompactSupport
    (g : GeneralLinear n K) (y : Fin n → K)
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)) :
    HasCompactSupport (fun u : upperUnipotent n K =>
      Φ (rectangularJoin (g.val * u.val.val) y)) :=
  Φ.hasCompactSupport.comp_isClosedEmbedding
    (isClosedEmbedding_rectangularUnipotentSlice g y)

/-- The actual Schwartz restriction along a rectangular unipotent slice. -/
def rectangularUnipotentSlice
    (g : GeneralLinear n K) (y : Fin n → K)
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)) :
    SchwartzBruhat (upperUnipotent n K) :=
  ⟨fun u => Φ (rectangularJoin (g.val * u.val.val) y),
    Φ.locallyConstant.comp_continuous
      (isClosedEmbedding_rectangularUnipotentSlice g y).continuous,
    rectangularUnipotentSlice_hasCompactSupport g y Φ⟩

@[simp] theorem rectangularUnipotentSlice_apply
    (g : GeneralLinear n K) (y : Fin n → K)
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (u : upperUnipotent n K) :
    rectangularUnipotentSlice g y Φ u = Φ (rectangularJoin (g.val * u.val.val) y) := rfl

/-- Any continuous complex weight preserves absolute convergence of a
Schwartz function on this closed slice, for every measure finite on compacts. -/
theorem rectangularUnipotentSlice_integrable
    [MeasurableSpace (upperUnipotent n K)] [BorelSpace (upperUnipotent n K)]
    (g : GeneralLinear n K) (y : Fin n → K)
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
    (a : upperUnipotent n K → ℂ) (ha : Continuous a)
    (μ : Measure (upperUnipotent n K)) [IsFiniteMeasureOnCompacts μ] :
    Integrable (fun u : upperUnipotent n K =>
      Φ (rectangularJoin (g.val * u.val.val) y) * a u) μ := by
  exact ((Φ.continuous.comp
    (isClosedEmbedding_rectangularUnipotentSlice g y).continuous).mul ha
      ).integrable_of_hasCompactSupport
        (rectangularUnipotentSlice_hasCompactSupport g y Φ).mul_right

section FourierConvergence

variable [MeasurableSpace K] [BorelSpace K] [LocallyCompactSpace K]
  [TotallyDisconnectedSpace K]

/-- Both integrability conjuncts of the adjacent-rank rectangular Fourier
identity, for any actual unipotent measure finite on compact sets. -/
theorem adjacentRankUnipotent_integrable
    (ψ : UnitaryAdditiveCharacter K) (ν : AdditiveHaarMeasure K)
    (hself : IsSelfDual ψ ν) (r : ℕ)
    [MeasurableSpace (upperUnipotent (r + 1) K)]
    [BorelSpace (upperUnipotent (r + 1) K)]
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) K))
    (μ : Measure (upperUnipotent (r + 1) K)) [IsFiniteMeasureOnCompacts μ] :
    Integrable (fun u : upperUnipotent (r + 1) K =>
      partialFourierEquiv ψ ν (r + 1) hself
        (rectangularTranslate (weylLong (r + 2) K * adjacentRankZeta K r) Φ)
          (rectangularJoin u.val.val (adjacentRankEpsilon K r)) *
            (inverseStandardCharacter ψ r u : ℂ)) μ ∧
    Integrable (fun u : upperUnipotent (r + 1) K =>
      rectangularFourierEquiv ψ ν (r + 1) (r + 2) hself
        (partialFourierEquiv ψ ν (r + 1) hself Φ)
          (rectangularJoin ((weylLong (r + 1) K).val * u.val.val)
            (Matrix.mulVec (weylLong (r + 1) K).val (adjacentRankEpsilon K r))) *
              (standardCharacter ψ r u : ℂ)) μ := by
  constructor
  · simpa only [Units.val_one, Matrix.one_mul] using
      rectangularUnipotentSlice_integrable (1 : GeneralLinear (r + 1) K)
        (adjacentRankEpsilon K r)
        (partialFourierEquiv ψ ν (r + 1) hself
          (rectangularTranslate (weylLong (r + 2) K * adjacentRankZeta K r) Φ))
        (fun u => (inverseStandardCharacter ψ r u : ℂ))
        (Units.continuous_val.comp (inverseStandardCharacterContinuous ψ r).continuous) μ
  · exact rectangularUnipotentSlice_integrable (weylLong (r + 1) K)
      (Matrix.mulVec (weylLong (r + 1) K).val (adjacentRankEpsilon K r))
      (rectangularFourierEquiv ψ ν (r + 1) (r + 2) hself
        (partialFourierEquiv ψ ν (r + 1) hself Φ))
      (fun u => (standardCharacter ψ r u : ℂ))
      (Units.continuous_val.comp (standardCharacterContinuous ψ r).continuous) μ

end FourierConvergence

end Langlands.HarmonicAnalysis
