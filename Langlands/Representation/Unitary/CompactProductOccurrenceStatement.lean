import Langlands.Representation.Unitary.InvariantSubspaceDiscreteDecompositionStatement

/-! # Irreducible occurrence in one factor of a compact-convolution product action -/

noncomputable section

open MeasureTheory
open scoped CompactlySupported

universe uG uD uE

namespace Langlands.Analysis

/-- In a pair of commuting unitary actions, compactness of the products of integrated
compactly supported weights implies that the first action has an irreducible closed
invariant subspace. -/
def CompactProductOccurrenceStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G]
    {D : Type uD} [Group D] [TopologicalSpace D] [IsTopologicalGroup D]
    [T2Space D] [LocallyCompactSpace D] [SecondCountableTopology D] [MeasurableSpace D]
    [BorelSpace D]
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
    (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure D) [ν.IsHaarMeasure]
    (σ : G →* (E →L[ℂ] E)) (τ : D →* (E →L[ℂ] E))
    (hσ : ∀ g x y, inner ℂ (σ g x) (σ g y) = inner ℂ x y)
    (hτ : ∀ d x y, inner ℂ (τ d x) (τ d y) = inner ℂ x y)
    (hσc : ∀ x, Continuous (fun g => σ g x)) (hτc : ∀ x, Continuous (fun d => τ d x)),
    (∀ g d, Commute (σ g) (τ d)) →
    (∀ (f : C_c(G, ℂ)) (hf : Integrable f μ) (b : C_c(D, ℂ)) (hb : Integrable b ν),
      IsCompactOperator
        ((integratedIsometricAction μ σ
          (fun g => (LinearMap.norm_map_iff_inner_map_map (σ g)).2 (hσ g))
          (fun x => (hσc x).stronglyMeasurable.aestronglyMeasurable) f hf).comp
        (integratedIsometricAction ν τ
          (fun d => (LinearMap.norm_map_iff_inner_map_map (τ d)).2 (hτ d))
          (fun x => (hτc x).stronglyMeasurable.aestronglyMeasurable) b hb))) →
    ∃ W : Submodule ℂ E, W ≠ ⊥ ∧ IsClosed (W : Set E) ∧
      (∀ g, ∀ x ∈ W, σ g x ∈ W) ∧
      ∀ P : Submodule ℂ E, P ≤ W → IsClosed (P : Set E) →
        (∀ g, ∀ x ∈ P, σ g x ∈ P) → P = ⊥ ∨ P = W

end Langlands.Analysis
