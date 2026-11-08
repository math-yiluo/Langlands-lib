import Langlands.Representation.Unitary.IntegratedOperator
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported

noncomputable section

universe uG uE

namespace Langlands.Analysis

open MeasureTheory
open scoped CompactlySupported

/-- A closed invariant subspace on which every compactly supported continuous
weight integrates the original unitary action to a compact operator is a
closed orthogonal sum of irreducible closed invariant subspaces, each
isomorphism class occurring finitely often. -/
def InvariantSubspaceDiscreteDecompositionStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (μ : Measure G) [μ.IsHaarMeasure]
    (π : G →* (E →L[ℂ] E))
    (hπinner : ∀ g x y, inner ℂ (π g x) (π g y) = inner ℂ x y)
    (hπcont : ∀ x : E, Continuous (fun g => π g x)),
    let hπnorm : ∀ (g : G) (x : E), ‖π g x‖ = ‖x‖ :=
      fun g => (LinearMap.norm_map_iff_inner_map_map (π g)).2 (hπinner g)
    let hπmeas : ∀ x : E, AEStronglyMeasurable (fun g => π g x) μ :=
      fun x => (hπcont x).stronglyMeasurable.aestronglyMeasurable
    ∀ (V : Submodule ℂ E), IsClosed (V : Set E) → (∀ (g : G), ∀ x ∈ V, π g x ∈ V) →
      (∀ (f : C_c(G, ℂ)) (hf : Integrable f μ),
        IsCompactOperator ((integratedIsometricAction μ π hπnorm hπmeas f hf).comp
          V.subtypeL)) →
      ∃ A : Set (Submodule ℂ E),
        (∀ P ∈ A, P ≤ V ∧ P ≠ ⊥ ∧ IsClosed (P : Set E) ∧
          (∀ (g : G), ∀ x ∈ P, π g x ∈ P) ∧
          ∀ Q : Submodule ℂ E, Q ≤ P → IsClosed (Q : Set E) →
            (∀ (g : G), ∀ x ∈ Q, π g x ∈ Q) → Q = ⊥ ∨ Q = P) ∧
        A.Pairwise (fun P Q => P ⟂ Q) ∧
        (sSup A).topologicalClosure = V ∧
        ∀ P ∈ A, ∀ hPi : (∀ (g : G), ∀ x ∈ P, π g x ∈ P),
          {Q : Submodule ℂ E | Q ∈ A ∧ ∃ U : P ≃ₗᵢ[ℂ] Q,
            ∀ (g : G) (x : P), (U ⟨π g x, hPi g x x.2⟩ : E) = π g (U x)}.Finite

end Langlands.Analysis
