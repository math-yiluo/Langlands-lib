import Langlands.Analysis.Meromorphic.AnalyticSystems
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-! # Fredholm's criterion for local finite type

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, §3.4:
the Lemma (Fredholm's criterion) and Corollary 3.4. -/

noncomputable section
set_option autoImplicit false

universe uE uM uB uC

namespace Langlands.Analysis.Meromorphic

open scoped Manifold

/-- Fredholm's criterion: if a holomorphic family `μ s` of operators between
complex Banach spaces is left invertible modulo compact operators at `s₀`, then
the kernels `ker (μ s)` form a family of finite type on an open neighborhood of
`s₀`. -/
def FredholmCriterionStatement : Prop :=
  ∀ {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {M : Type uM} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M]
    {B : Type uB} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    {C : Type uC} [NormedAddCommGroup C] [NormedSpace ℂ C] [CompleteSpace C]
    (μ : M → B →L[ℂ] C) (s₀ : M),
    IsHolomorphicOperatorFamilyOn 𝓘(ℂ, E) μ Set.univ →
    (∃ D : C →L[ℂ] B, IsCompactOperator (D ∘L μ s₀ - ContinuousLinearMap.id ℂ B)) →
    ∃ U : Set M, IsOpen U ∧ s₀ ∈ U ∧
      IsFiniteTypeOn 𝓘(ℂ, E) (fun s => {v : B | μ s v = 0}) U

/-- Corollary 3.4: for holomorphic families `μ s`, `ν s` of operators between
complex Hilbert spaces with `μ s₀` a topological embedding and `ν s₀` compact,
the solution sets of `μ s v = ν s v` form a family of finite type on an open
neighborhood of `s₀`. -/
def HilbertFredholmCriterionStatement : Prop :=
  ∀ {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {M : Type uM} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M]
    {B : Type uB} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
    {C : Type uC} [NormedAddCommGroup C] [InnerProductSpace ℂ C] [CompleteSpace C]
    (μ ν : M → B →L[ℂ] C) (s₀ : M),
    IsHolomorphicOperatorFamilyOn 𝓘(ℂ, E) μ Set.univ →
    IsHolomorphicOperatorFamilyOn 𝓘(ℂ, E) ν Set.univ →
    Topology.IsEmbedding (μ s₀) → IsCompactOperator (ν s₀) →
    ∃ U : Set M, IsOpen U ∧ s₀ ∈ U ∧
      IsFiniteTypeOn 𝓘(ℂ, E) (fun s => {v : B | μ s v = ν s v}) U

/-- The Lemma (Fredholm's criterion) and Corollary 3.4 of Bernstein–Lapid. -/
def FredholmFiniteTypeStatement : Prop :=
  FredholmCriterionStatement.{uE, uM, uB, uC} ∧ HilbertFredholmCriterionStatement.{uE, uM, uB, uC}

end Langlands.Analysis.Meromorphic
