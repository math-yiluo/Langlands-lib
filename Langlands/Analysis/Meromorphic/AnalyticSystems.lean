import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-! # Holomorphic and meromorphic vector-valued functions and analytic linear systems

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, §3.1–3.3:
weakly holomorphic functions on a complex manifold with values in a topological
vector space, meromorphic functions with local scalar denominators, analytic
families of operators, analytic systems of linear equations and the finite-type
conditions on their solution sets. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

/-- A function `f : M → V` is holomorphic on `U` when `s ↦ μ (f s)` is complex
differentiable on `U` for every continuous linear form `μ` on `V`
(Bernstein–Lapid §3.1). -/
def IsHolomorphicOn (f : M → V) (U : Set M) : Prop :=
  ∀ μ : V →L[ℂ] ℂ, MDifferentiableOn I 𝓘(ℂ, ℂ) (fun s => μ (f s)) U

/-- A function `f`, holomorphic on the open dense set `U`, is meromorphic on `M`
when every point has an open connected neighborhood `W` with a holomorphic
scalar `g`, not identically zero on `W`, and a holomorphic `h : M → V` on `W`
such that `g s • f s = h s` for all `s ∈ U ∩ W` (Bernstein–Lapid §3.1). -/
def IsMeromorphicOn (f : M → V) (U : Set M) : Prop :=
  IsOpen U ∧ Dense U ∧ IsHolomorphicOn I f U ∧
    ∀ s₀ : M, ∃ W : Set M, IsOpen W ∧ IsConnected W ∧ s₀ ∈ W ∧
      ∃ (g : M → ℂ) (h : M → V), MDifferentiableOn I 𝓘(ℂ, ℂ) g W ∧
        (∃ s ∈ W, g s ≠ 0) ∧ IsHolomorphicOn I h W ∧
        ∀ s ∈ U ∩ W, g s • f s = h s

/-- A family of continuous linear operators `A s : V → V₂` is holomorphic on `U`
when `s ↦ A s v` is holomorphic on `U` for every `v` (Bernstein–Lapid §3.2). -/
def IsHolomorphicOperatorFamilyOn {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂]
    [TopologicalSpace V₂] (A : M → V →L[ℂ] V₂) (U : Set M) : Prop :=
  ∀ v : V, IsHolomorphicOn I (fun s => A s v) U

/-- A family `A s` of subsets of `V` is of finite type on `U` when there are a
finite-dimensional space `ℂⁿ` and a holomorphic family of injective operators
`ℓ s : ℂⁿ → V` on `U` with `A s ⊆ range (ℓ s)` for all `s ∈ U`
(Bernstein–Lapid §3.3, Definition (2)). -/
def IsFiniteTypeOn (A : M → Set V) (U : Set M) : Prop :=
  ∃ (n : ℕ) (ℓ : M → (Fin n → ℂ) →L[ℂ] V), IsHolomorphicOperatorFamilyOn I ℓ U ∧
    (∀ s ∈ U, Function.Injective (ℓ s)) ∧ ∀ s ∈ U, A s ⊆ Set.range (ℓ s)

/-- A family of subsets is locally of finite type when every point has an open
neighborhood on which it is of finite type (Bernstein–Lapid §3.3,
Definition (3)). -/
def IsLocallyFiniteType (A : M → Set V) : Prop :=
  ∀ s₀ : M, ∃ U : Set M, IsOpen U ∧ s₀ ∈ U ∧ IsFiniteTypeOn I A U

/-- A subset `Z` of `M` is analytic when every point has an open neighborhood
`U` and finitely many functions holomorphic on `U` whose common zeros in `U`
are exactly `Z ∩ U`. -/
def IsAnalyticSubset (Z : Set M) : Prop :=
  ∀ s₀ : M, ∃ U : Set M, IsOpen U ∧ s₀ ∈ U ∧ ∃ (k : ℕ) (g : Fin k → M → ℂ),
    (∀ j, MDifferentiableOn I 𝓘(ℂ, ℂ) (g j) U) ∧ Z ∩ U = {s ∈ U | ∀ j, g j s = 0}

section Systems

variable {ι : Type*} {F : ι → Type*} [∀ i, AddCommGroup (F i)] [∀ i, Module ℂ (F i)]
  [∀ i, TopologicalSpace (F i)]

/-- The solution set at `s` of the system of linear equations
`μ i s v = c i s`, `i ∈ ι`, on `v ∈ V` (Bernstein–Lapid §3.3). -/
def systemSolutions (μ : ∀ i, M → V →L[ℂ] F i) (c : ∀ i, M → F i) (s : M) : Set V :=
  {v | ∀ i, μ i s v = c i s}

/-- The system `μ i s v = c i s` depends analytically on `s`: every `μ i` is a
holomorphic family of operators and every `c i` is holomorphic on `M`
(Bernstein–Lapid §3.3, Definition (1)). -/
def IsAnalyticSystem (μ : ∀ i, M → V →L[ℂ] F i) (c : ∀ i, M → F i) : Prop :=
  (∀ i, IsHolomorphicOperatorFamilyOn I (μ i) Set.univ) ∧
    ∀ i, IsHolomorphicOn I (c i) Set.univ

/-- The set `M_unq` of parameters at which the system has exactly one solution
(Bernstein–Lapid, Theorem 3.3). -/
def uniqueSolutionLocus (μ : ∀ i, M → V →L[ℂ] F i) (c : ∀ i, M → F i) : Set M :=
  {s | ∃ v : V, systemSolutions μ c s = {v}}

end Systems

end Langlands.Analysis.Meromorphic
