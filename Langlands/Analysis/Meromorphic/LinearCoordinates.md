# Holomorphy and meromorphy in linear coordinates

Module `Langlands.Analysis.Meromorphic.LinearCoordinates` defines holomorphic
and meromorphic functions on a finite-dimensional complex vector space `X`
that carries no chosen topology or norm. It reuses the predicates
`IsHolomorphicOn` and `IsMeromorphicOn` of
`Langlands.Analysis.Meromorphic.AnalyticSystems` (Bernstein–Lapid §3.1) on the
coordinate spaces `ℂⁿ`. It supplies no theorem.

## Purpose and source

In Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, the parameter space
of Eisenstein series is the complex vector space
`𝔛_P = X^*(M) ⊗_ℤ ℂ = 𝔞_P^* ⊗_ℝ ℂ` of §2.1 (journal p.190), and Theorem 2.3
(p.191) asserts that `λ ↦ E(φ, λ)` is meromorphic on `𝔛_P`. As in §3
(p.192), `𝔛_P` is used as a complex analytic manifold: a finite-dimensional
complex vector space, with its unique vector-space topology and complex
structure. The Library constructs `X^*(M) ⊗ ℂ` as a bare complex module
(`Langlands.Global.AdelicGroupPoints.ComplexCharacterParameter`). The
definitions here make "holomorphic" and "meromorphic" meaningful on such a
module without choosing a norm or charts on it. This coordinate formulation is
internal; the mathematical notions are those of the source.

## Definitions

Let `X` be a complex vector space (`Module ℂ X`), `V` a complex vector space
with a topology, `f : X → V` and `U ⊆ X`.

- `IsHolomorphicInCoordinatesOn f U`: `X` is finite-dimensional over `ℂ`, and
  for every `n` and every complex linear isomorphism `e : ℂⁿ ≃ X`
  (`(Fin n → ℂ) ≃ₗ[ℂ] X`), the function `f ∘ e` is holomorphic on `e ⁻¹' U`
  in the sense of `IsHolomorphicOn 𝓘(ℂ, Fin n → ℂ)`: for every continuous
  linear form `μ` on `V`, `μ ∘ f ∘ e` is complex differentiable on `e ⁻¹' U`.
- `IsMeromorphicInCoordinatesOn f U`: `X` is finite-dimensional over `ℂ`, and
  for every such `e`, the function `f ∘ e` is meromorphic on `ℂⁿ` with domain
  of holomorphy `e ⁻¹' U` in the sense of `IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ)`:
  `e ⁻¹' U` is open and dense, `f ∘ e` is holomorphic on it, and every point
  of `ℂⁿ` has a connected open neighborhood `W` with a scalar `g` holomorphic
  on `W` and not identically zero on `W`, and an `h` holomorphic on `W`, such
  that `g · (f ∘ e) = h` on `e ⁻¹' U ∩ W`.

`ℂⁿ` is `Fin n → ℂ` with its product (sup) norm, as a manifold modelled on
itself.

## Conventions

The coordinate maps are all complex linear isomorphisms, not a chosen basis.
Two such isomorphisms differ by an element of `GL_n(ℂ)`, which is
biholomorphic, so requiring the condition for all of them is equivalent to
requiring it for one; this equivalence is not proved here. Openness and
density of `U` are expressed in coordinates and are likewise independent of
the coordinates, because linear isomorphisms of finite-dimensional normed
spaces are homeomorphisms. If `X` is not finite-dimensional the predicates
are false, not vacuously true; that is why finite dimensionality is a
conjunct. Every `n` is quantified, but an isomorphism `ℂⁿ ≃ X` exists only
for `n = dim X`.

## Scope

No theorem about these predicates (independence of coordinates, behaviour
under linear maps, comparison with any topology on `X`) is asserted here.
