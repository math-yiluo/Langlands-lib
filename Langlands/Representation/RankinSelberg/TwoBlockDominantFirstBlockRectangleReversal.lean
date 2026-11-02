import Langlands.Representation.RankinSelberg.Measures
import Mathlib.Data.Fin.Rev
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Supplied-Haar reversal of both rectangle indices -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantFirstBlock

open MeasureTheory HarmonicAnalysis

universe uK uE

variable (K : Type uK) [MeasurableSpace K]

/-- Reverse both finite indices, as a measurable equivalence. -/
def firstBlockRectangleReversalEquiv (a b : ℕ) :
    Matrix (Fin a) (Fin b) K ≃ᵐ Matrix (Fin a) (Fin b) K :=
  MeasurableEquiv.arrowCongr' Fin.revPerm
    (MeasurableEquiv.arrowCongr' Fin.revPerm (MeasurableEquiv.refl K))

@[simp] theorem firstBlockRectangleReversalEquiv_apply (a b : ℕ)
    (Y : Matrix (Fin a) (Fin b) K) :
    firstBlockRectangleReversalEquiv K a b Y = Y.submatrix Fin.rev Fin.rev := rfl

variable [AddGroup K] [TopologicalSpace K]
variable (ν : AdditiveHaarMeasure K) [SigmaFinite ν.measure]

/-- Simultaneous row and column reversal preserves every supplied rectangle
product measure, including in either zero dimension. -/
theorem measurePreserving_firstBlockRectangleReversalEquiv (a b : ℕ) :
    MeasurePreserving (firstBlockRectangleReversalEquiv K a b)
      (rectangularMeasure ν a b) (rectangularMeasure ν a b) := by
  have hrow := measurePreserving_arrowCongr' (fun _ : Fin b => ν.measure)
    (fun _ : Fin b => ν.measure) Fin.revPerm (MeasurableEquiv.refl K)
    (fun _ => MeasurePreserving.id _)
  exact measurePreserving_arrowCongr'
    (fun _ : Fin a => Measure.pi (fun _ : Fin b => ν.measure))
    (fun _ : Fin a => Measure.pi (fun _ : Fin b => ν.measure))
    Fin.revPerm (MeasurableEquiv.arrowCongr' Fin.revPerm (MeasurableEquiv.refl K))
    (fun _ => hrow)

/-- The exact matrix-submatrix formulation of supplied-Haar reversal. -/
theorem measurePreserving_firstBlockRectangleReversal (a b : ℕ) :
    MeasurePreserving (fun Y : Matrix (Fin a) (Fin b) K =>
      Y.submatrix Fin.rev Fin.rev) (rectangularMeasure ν a b) (rectangularMeasure ν a b) :=
  measurePreserving_firstBlockRectangleReversalEquiv K ν a b

/-- A Prop-valued record of invariance in all finite rectangle dimensions. -/
def HasRectangleReversalInvariance : Prop :=
  ∀ a b : ℕ, MeasurePreserving (fun Y : Matrix (Fin a) (Fin b) K =>
    Y.submatrix Fin.rev Fin.rev) (rectangularMeasure ν a b) (rectangularMeasure ν a b)

/-- Every supplied sigma-finite additive Haar has rectangle-reversal invariance. -/
theorem hasRectangleReversalInvariance : HasRectangleReversalInvariance K ν :=
  measurePreserving_firstBlockRectangleReversal K ν

/-- Total Bochner change of variables for both reversed rectangle indices.
Actual convergence is transported by the separate integrability equivalence. -/
theorem integral_firstBlockRectangleReversal
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : ℕ) (φ : Matrix (Fin a) (Fin b) K → E) :
    (∫ Y, φ (Y.submatrix Fin.rev Fin.rev) ∂rectangularMeasure ν a b) =
      ∫ Y, φ Y ∂rectangularMeasure ν a b :=
  (measurePreserving_firstBlockRectangleReversalEquiv K ν a b).integral_comp
    (firstBlockRectangleReversalEquiv K a b).measurableEmbedding φ

/-- Actual rectangle integrability is equivalent in both directions under reversal. -/
theorem integrable_firstBlockRectangleReversal_iff
    {E : Type uE} [NormedAddCommGroup E]
    (a b : ℕ) (φ : Matrix (Fin a) (Fin b) K → E) :
    Integrable (fun Y => φ (Y.submatrix Fin.rev Fin.rev)) (rectangularMeasure ν a b) ↔
      Integrable φ (rectangularMeasure ν a b) :=
  (measurePreserving_firstBlockRectangleReversalEquiv K ν a b).integrable_comp_emb
    (firstBlockRectangleReversalEquiv K a b).measurableEmbedding

end Langlands.RankinSelberg.TwoBlockDominantFirstBlock
