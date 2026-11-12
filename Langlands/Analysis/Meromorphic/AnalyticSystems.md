# Holomorphic and meromorphic vector-valued functions and analytic linear systems

Module `Langlands.Analysis.Meromorphic.AnalyticSystems` defines the objects of
Bernstein–Lapid §3.1–3.3. They are needed to state the principle of
meromorphic continuation (Theorem 3.3), which the paper uses to continue
Eisenstein series and intertwining operators. The module contains
definitions only and proves nothing.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), 187–234, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`. Locators refer to
the journal PDF `Bernstein-Lapid--On the meromorphic continuation of
Eisenstein series--2024.pdf` in the registered folder:

- §3.1, p.192: analytic (holomorphic) functions with values in a locally
  convex space, and meromorphic functions;
- §3.2, p.193: analytic families of operators;
- §3.3, pp.193–194: systems of linear equations, their solution sets
  `Sol(Ξ)`, and the Definition with items (1)–(4) (analytic families of
  systems, finite type, locally finite type, finite type of a system);
- Theorem 3.3, p.194: the set `M_unq`.

## Setting and conventions

The parameter space is a manifold `M` charted on `H` with a model with corners
`I : ModelWithCorners ℂ E H` over `ℂ`. The model `I` is an explicit argument of
each predicate, as in Mathlib's `MDifferentiableOn I I'`. A scalar function
`g : M → ℂ` is holomorphic on `U` when `MDifferentiableOn I 𝓘(ℂ, ℂ) g U`, that is,
complex differentiable in charts. Bernstein–Lapid take `M` to be a complex
analytic manifold. The statement module specializes to `I = 𝓘(ℂ, E)` with
`E` finite-dimensional and `IsManifold 𝓘(ℂ, E) 1 M`.

All sets carrying a holomorphy condition below are open where the predicates
are used (in `IsMeromorphicOn` openness of `U` is part of the definition, in
`IsLocallyFiniteType` the neighborhoods are open). On an open set,
`MDifferentiableOn` is holomorphy of the restriction to the open submanifold.

Vector spaces `V`, `V₂` and `F i` are complex vector spaces with a topology.
The predicates here do not need the Hausdorff, locally convex or
topological-vector-space hypotheses of the source. The principle of
meromorphic continuation states those hypotheses itself. Operators are
continuous complex-linear maps `→L[ℂ]`, as in the source ("by an operator from
E to F we will always mean a continuous linear map").

## Definitions

- `IsHolomorphicOn I f U` for `f : M → V`: for every continuous linear form
  `μ : V →L[ℂ] ℂ`, the scalar function `s ↦ μ (f s)` is holomorphic on `U`.
  This is the definition of §3.1: `f` is analytic if `⟨μ, f(s)⟩` is analytic
  for every `μ ∈ E′`. Continuity of `f` is a consequence in the source's
  setting (cited there from Grothendieck), not part of the definition.
- `IsMeromorphicOn I f U` for `f : M → V`: `U` is open and dense, `f` is
  holomorphic on `U`, and every `s₀ ∈ M` has an open connected neighborhood
  `W` with a scalar `g` holomorphic on `W` and not identically zero on `W`, and
  an `h : M → V` holomorphic on `W`, such that `g s • f s = h s` for all
  `s ∈ U ∩ W`. This is the definition of §3.1, where `f` is defined only on
  `U`. Here `f` is a function on all of `M` and only its values on `U` matter.
  The source's "connected neighborhood" is read as an open connected
  neighborhood, the domain of the holomorphic functions `g` and `h`.
- `IsHolomorphicOperatorFamilyOn I A U` for `A : M → V →L[ℂ] V₂`: for every
  `v : V`, `s ↦ A s v` is holomorphic on `U`. In §3.2 a holomorphic family is a
  holomorphic map into `L_s(E, F)`, the operators with the topology of
  pointwise convergence. The source shows this is equivalent to holomorphy of
  every `s ↦ A_s(v)` and then uses that formulation ("we will simply say that
  `A_s` is a holomorphic family of operators"). The Lean definition is that
  formulation.
- `IsFiniteTypeOn I A U` for a family `A : M → Set V`: there are `n : ℕ` and
  `ℓ : M → (Fin n → ℂ) →L[ℂ] V`, a holomorphic family of operators on `U`,
  with every `ℓ s` (`s ∈ U`) injective and `A s ⊆ range (ℓ s)`. This is
  Definition (2) of §3.3, on the open submanifold `U`. The source's
  finite-dimensional space `L` is replaced by `ℂⁿ`, `n = dim L`. Every
  finite-dimensional complex vector space with its Hausdorff vector topology
  is isomorphic to `ℂⁿ`, and composing with that isomorphism preserves
  holomorphy, injectivity and ranges.
- `IsLocallyFiniteType I A`: every `s₀ ∈ M` has an open neighborhood `U` with
  `IsFiniteTypeOn I A U`. This is Definition (3) of §3.3.
- `IsAnalyticSubset I Z`: every `s₀ ∈ M` has an open neighborhood `U` and
  finitely many functions `g j`, holomorphic on `U`, with
  `Z ∩ U = {s ∈ U | g j s = 0 for all j}`.
- `systemSolutions μ c s` for `μ : ∀ i, M → V →L[ℂ] F i` and
  `c : ∀ i, M → F i`: the set of `v : V` with `μ i s v = c i s` for every
  `i : ι`. This is `Sol(Ξ(s))` for the system `Ξ(s)` of §3.3, Definition
  (1), with the triples `(F_i, μ_i, c_i)` given as the families `F`, `μ`, `c`
  over an arbitrary index type `ι`.
- `IsAnalyticSystem I μ c`: each `μ i` is a holomorphic family of operators
  on `M` and each `c i` is holomorphic on `M`. This is Definition (1) of §3.3
  ("the system depends analytically on `s`").
- `uniqueSolutionLocus μ c`: the set of `s` with `systemSolutions μ c s = {v}`
  for some `v`. This is `M_unq` of Theorem 3.3.

Definition (4) of §3.3 (a system is locally of finite type if its solution
sets are) is not a separate declaration. It is expressed as
`IsLocallyFiniteType I (systemSolutions μ c)`.

## Provenance of `IsAnalyticSubset`

Theorem 3.3 asserts that the complement of `M_unq` is "analytic" without
defining the word. `IsAnalyticSubset` formalizes the standard notion of a
(closed) analytic subset of a complex manifold: locally the common zero set of
finitely many holomorphic functions. Its provenance is internal. Such a set is
closed. A family of holomorphic functions with possibly infinitely many members
also defines analytic common zero sets, but only by the Noetherian property of
rings of convergent power series. That property is not used in this
definition.
