import Langlands.Analysis.OperatorTrace
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Traces of trace-class operators along closed subspaces and Hilbert sums

This module states, without proof, how the Library's `operatorTrace` of a trace-class operator
splits along a closed subspace containing its range and along a Hilbert sum decomposition.
These are the steps that turn the trace of a convolution operator on `L²` into the sum of its
traces on the irreducible summands of the cuspidal spectrum (the spectral side of the simple
trace formula), and the twisted variant used for base change.
-/

noncomputable section

namespace Langlands.Analysis.OperatorIdeals

universe u v

/-- Traces along subspaces and Hilbert sums.

Let `E` be a complex Hilbert space and `B` a trace-class operator on `E`. For a complete
subspace `W` of `E`, the compression of `B` to `W` is `P_W ∘ B ∘ ι_W : W →L[ℂ] W`, where `ι_W`
is the inclusion and `P_W` the orthogonal projection onto `W`.

1. If `S` is a complete subspace of `E` that contains the range of `B`, then the compression of
   `B` to `S` is trace class and has the same trace as `B`.
2. If `E` is the Hilbert sum of complete subspaces `W i`, then every compression of `B` to a
   `W i` is trace class, their traces are absolutely summable, and their sum is the trace of `B`.
3. If moreover `B` maps each `W i` into `W (τ i)` for a map `τ`, then the sum of the traces of
   the compressions over the indices fixed by `τ` is the trace of `B`. -/
def HilbertSumTraceStatement : Prop :=
  (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (S : Submodule ℂ E) [CompleteSpace S] (B : E →L[ℂ] E),
      IsTraceClass B → (∀ x, B x ∈ S) →
        IsTraceClass (S.orthogonalProjectionOnto ∘L B ∘L S.subtypeL) ∧
        operatorTrace (S.orthogonalProjectionOnto ∘L B ∘L S.subtypeL) = operatorTrace B) ∧
  (∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      (ι : Type v) (W : ι → Submodule ℂ E) [∀ i, CompleteSpace (W i)],
      IsHilbertSum ℂ (fun i => W i) (fun i => (W i).subtypeₗᵢ) →
      ∀ (B : E →L[ℂ] E), IsTraceClass B →
        (∀ i, IsTraceClass ((W i).orthogonalProjectionOnto ∘L B ∘L (W i).subtypeL)) ∧
        Summable (fun i =>
          ‖operatorTrace ((W i).orthogonalProjectionOnto ∘L B ∘L (W i).subtypeL)‖) ∧
        HasSum (fun i => operatorTrace ((W i).orthogonalProjectionOnto ∘L B ∘L (W i).subtypeL))
          (operatorTrace B) ∧
        ∀ τ : ι → ι, (∀ i, ∀ x ∈ W i, B x ∈ W (τ i)) →
          HasSum (fun i : {i // τ i = i} =>
              operatorTrace ((W i.1).orthogonalProjectionOnto ∘L B ∘L (W i.1).subtypeL))
            (operatorTrace B))

end Langlands.Analysis.OperatorIdeals
