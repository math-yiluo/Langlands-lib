import Langlands.Topology.RenardRealSequenceCompletion
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Concrete completion and continuous nonextension statements

These closed propositions are internal fixed-real tests motivated by Renard,
Appendix A.III.1, example 2 (2026 edition, printed p.252 / PDF258).
They state proof obligations over the published actual sequence spaces and
canonical maps. They supply no proofs or source correction.
-/

set_option autoImplicit false

namespace Langlands.Renard.RealSequenceCompletion

/-- Every sequence is the product-topology limit of its actual finite truncations. -/
def TruncationsConverge : Prop :=
  ∀ p : ProductSequence,
    Filter.Tendsto (fun n : ℕ => inclusion (truncate n p)) Filter.atTop (nhds p)

/-- The actual inclusion of the inherited finite-support subspace has dense range. -/
def InclusionDenseRange : Prop :=
  DenseRange (inclusion : FiniteSequence → ProductSequence)

/-- The constant-one sequence does not belong to the actual finite-support submodule. -/
def MissingSequenceOutsideSubmodule : Prop :=
  missingSequence ∉ finiteSequenceSubmodule

/-- The constant-one sequence is outside the range of the actual inclusion. -/
def MissingSequenceOutsideInclusion : Prop :=
  missingSequence ∉ Set.range (inclusion : FiniteSequence → ProductSequence)

/-- The finite-support subspace is incomplete for its inherited uniformity. -/
def FiniteSequenceIncomplete : Prop :=
  ¬ CompleteSpace FiniteSequence

/-- The explicit compatible metric has positive distance to the missing sequence. -/
def DistanceToMissingPositive : Prop :=
  ∀ x : FiniteSequence, 0 < sequenceDistance (inclusion x) missingSequence

/-- The total real reciprocal-distance function is continuous in the inherited topology. -/
def ReciprocalDistanceContinuous : Prop :=
  Continuous reciprocalDistance

/-- The named actual completion map is a real continuous linear equivalence,
with its specified agreement on the canonical image of the finite subspace. -/
def CompletionProductComparison : Prop :=
  ∃ e : SequenceCompletion ≃L[ℝ] ProductSequence,
    (e : SequenceCompletion → ProductSequence) =
        (completionToProduct : SequenceCompletion → ProductSequence) ∧
      ∀ x : FiniteSequence, e (toCompletion x) = inclusion x

/-- Mathlib's existing real scalar action on the actual completion is jointly continuous. -/
def CompletionJointScalarContinuity : Prop :=
  ContinuousSMul ℝ SequenceCompletion

/-- No arbitrary continuous real-valued function on the product extends the reciprocal. -/
def NoProductContinuousExtension : Prop :=
  ¬ ∃ g : ProductSequence → ℝ,
    Continuous g ∧ ∀ x : FiniteSequence, g (inclusion x) = reciprocalDistance x

/-- No arbitrary continuous real-valued function on the actual usual completion
extends the reciprocal along the actual canonical completion arrow. -/
def NoCompletionContinuousExtension : Prop :=
  ¬ ∃ g : SequenceCompletion → ℝ,
    Continuous g ∧ ∀ x : FiniteSequence, g (toCompletion x) = reciprocalDistance x

/-- All concrete completion and continuous nonextension obligations, without premises. -/
def CompletionCounterexampleStatements : Prop :=
  TruncationsConverge ∧
    InclusionDenseRange ∧
    MissingSequenceOutsideSubmodule ∧
    MissingSequenceOutsideInclusion ∧
    FiniteSequenceIncomplete ∧
    DistanceToMissingPositive ∧
    ReciprocalDistanceContinuous ∧
    CompletionProductComparison ∧
    CompletionJointScalarContinuity ∧
    NoProductContinuousExtension ∧
    NoCompletionContinuousExtension

end Langlands.Renard.RealSequenceCompletion
