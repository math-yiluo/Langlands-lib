import Langlands.Analysis.Meromorphic.AnalyticSystems
import Mathlib.Analysis.LocallyConvex.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-! # The principle of meromorphic continuation

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*,
Theorem 3.3. -/

noncomputable section
set_option autoImplicit false

universe uE uM uV uι uF

namespace Langlands.Analysis.Meromorphic

open scoped Manifold

/-- Parts (2), (3) and the openness in part (1) of the principle of meromorphic
continuation: for an analytic system of linear equations on a complex Hausdorff
locally convex space, parametrized by a connected finite-dimensional complex
manifold and locally of finite type, if the locus `M_unq` of parameters with a
unique solution `v s` has nonempty interior, then `M_unq` is open, `v` is
holomorphic on `M_unq` and meromorphic on `M`. -/
def MeromorphicContinuationHolomorphicStatement : Prop :=
  ∀ {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {M : Type uM} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M]
    [ConnectedSpace M]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℂ V]
    [LocallyConvexSpace ℝ V] [T2Space V]
    {ι : Type uι} {F : ι → Type uF} [∀ i, AddCommGroup (F i)] [∀ i, Module ℂ (F i)]
    [∀ i, Module ℝ (F i)] [∀ i, IsScalarTower ℝ ℂ (F i)] [∀ i, TopologicalSpace (F i)]
    [∀ i, IsTopologicalAddGroup (F i)] [∀ i, ContinuousSMul ℂ (F i)]
    [∀ i, LocallyConvexSpace ℝ (F i)] [∀ i, T2Space (F i)]
    (μ : ∀ i, M → V →L[ℂ] F i) (c : ∀ i, M → F i),
    IsAnalyticSystem 𝓘(ℂ, E) μ c →
    IsLocallyFiniteType 𝓘(ℂ, E) (systemSolutions μ c) →
    (interior (uniqueSolutionLocus μ c)).Nonempty →
    ∃ v : M → V,
      (∀ s ∈ uniqueSolutionLocus μ c, systemSolutions μ c s = {v s}) ∧
      IsOpen (uniqueSolutionLocus μ c) ∧
      IsHolomorphicOn 𝓘(ℂ, E) v (uniqueSolutionLocus μ c) ∧
      IsMeromorphicOn 𝓘(ℂ, E) v (uniqueSolutionLocus μ c)

/-- The remaining assertion of part (1) of the principle of meromorphic
continuation: under the same hypotheses, the complement of the locus `M_unq` of
parameters with a unique solution is an analytic subset of `M`. -/
def MeromorphicContinuationAnalyticComplementStatement : Prop :=
  ∀ {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {M : Type uM} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M]
    [ConnectedSpace M]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℂ V]
    [LocallyConvexSpace ℝ V] [T2Space V]
    {ι : Type uι} {F : ι → Type uF} [∀ i, AddCommGroup (F i)] [∀ i, Module ℂ (F i)]
    [∀ i, Module ℝ (F i)] [∀ i, IsScalarTower ℝ ℂ (F i)] [∀ i, TopologicalSpace (F i)]
    [∀ i, IsTopologicalAddGroup (F i)] [∀ i, ContinuousSMul ℂ (F i)]
    [∀ i, LocallyConvexSpace ℝ (F i)] [∀ i, T2Space (F i)]
    (μ : ∀ i, M → V →L[ℂ] F i) (c : ∀ i, M → F i),
    IsAnalyticSystem 𝓘(ℂ, E) μ c →
    IsLocallyFiniteType 𝓘(ℂ, E) (systemSolutions μ c) →
    (interior (uniqueSolutionLocus μ c)).Nonempty →
    IsAnalyticSubset 𝓘(ℂ, E) (uniqueSolutionLocus μ c)ᶜ

/-- The principle of meromorphic continuation (Bernstein–Lapid, Theorem 3.3):
the conjunction of its two parts above. -/
def MeromorphicContinuationPrincipleStatement : Prop :=
  MeromorphicContinuationHolomorphicStatement.{uE, uM, uV, uι, uF} ∧
    MeromorphicContinuationAnalyticComplementStatement.{uE, uM, uV, uι, uF}

end Langlands.Analysis.Meromorphic
