import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! # Regrouping a Hilbert sum along finite fibres -/

set_option autoImplicit false

universe uK uH uI uB

namespace Langlands.Analysis

/-- The sums over the finite fibres of a labelling of an internal Hilbert sum are closed
and give another internal Hilbert sum. The new projections are the finite sums of the
original projections, and each new summand is invariant under maps preserving the
original summands. -/
def OrthogonalHilbertSumFiniteRegroupingStatement : Prop :=
  ∀ (𝕜 : Type uK) [RCLike 𝕜]
    (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (I : Type uI) (B : Type uB) (P : I → Submodule 𝕜 H) [∀ i, CompleteSpace (P i)]
    (label : I → B) [∀ b, Fintype {i : I // label i = b}],
    IsHilbertSum 𝕜 (fun i => ↥(P i)) (fun i => (P i).subtypeₗᵢ) →
    let Q (b : B) := ⨆ i : {i : I // label i = b}, P i.val
    IsHilbertSum 𝕜 (fun b => ↥(Q b)) (fun b => (Q b).subtypeₗᵢ) ∧
    (∀ (T : H →ₗ[𝕜] H), (∀ i x, x ∈ P i → T x ∈ P i) →
      ∀ b x, x ∈ Q b → T x ∈ Q b) ∧
    ∃ hClosed : ∀ b, IsClosed (Q b : Set H),
      ∀ (b : B) (x : H),
        letI : CompleteSpace (Q b) := (hClosed b).completeSpace_coe
        (Q b).starProjection x = ∑ i : {i : I // label i = b}, (P i.val).starProjection x

end Langlands.Analysis
