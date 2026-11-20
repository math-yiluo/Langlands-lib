# Enlarging the domain of holomorphy of a meromorphic family

Module `Langlands.Analysis.SeveralComplex.MeromorphicDomainExtension`
(namespace `Langlands.Analysis.Meromorphic`). It states and proves the
proposition `MeromorphicDomainExtensionStatement` (proof
`meromorphicDomainExtension`), with the lemmas below. Everything is proved;
there are no premises.

## Purpose and provenance

This is a helper for Task 5613 (Lapid 2011, Proposition 6:
`Langlands.Global.EisensteinImaginaryAxisHolomorphyStatement`). Its conclusion
has the shape of that target: a family `E λ g`, meromorphic in `λ` with one
domain of holomorphy `D` for all `g`, is replaced by a representative `E'` of
the same meromorphic functions whose domain of holomorphy `D'` contains a
prescribed set `Λ` (there: the imaginary parameters `i𝔞_P^*`), provided that
near every point of `Λ` the functions `E(·, g)` extend holomorphically across
the singular set, on one neighbourhood for all `g`.

Provenance: internal. The content is the elementary fact that holomorphic
extensions of a function from a dense open set are unique where they exist,
so local extensions glue, together with the invariance of
`IsMeromorphicOn` under linear changes of coordinates. It is not taken from a
particular source; it uses only the definitions `IsHolomorphicOn`,
`IsMeromorphicOn` (module `Langlands.Analysis.Meromorphic.AnalyticSystems`,
Bernstein–Lapid §3.1) and `IsMeromorphicInCoordinatesOn` (module
`Langlands.Analysis.Meromorphic.LinearCoordinates`).

## Statement

`MeromorphicDomainExtensionStatement`: for a complex vector space `X : Type`,
an index type `Γ : Type`, `E : X → Γ → ℂ` and `D : Set X` such that
`λ ↦ E λ g` is meromorphic with domain of holomorphy `D` in linear
coordinates for every `g` (`IsMeromorphicInCoordinatesOn`), and sets
`O Λ : Set X`, suppose that for every `λ₀ ∈ Λ` there are `n`, a linear
isomorphism `e : (Fin n → ℂ) ≃ₗ[ℂ] X` and an open `W ⊆ ℂⁿ` with
`e⁻¹ λ₀ ∈ W` and `e(W) ⊆ O`, such that for every `g` some `h` complex
differentiable on `W` satisfies `h s = E (e s) g` whenever `s ∈ W` and
`e s ∈ D`. Then there are `E'` and `D'` with

1. `Λ ⊆ D'` and `D ⊆ D'`;
2. `λ ↦ E' λ g` meromorphic with domain of holomorphy `D'` in linear
   coordinates, for every `g`;
3. `E' λ = E λ` for every `λ ∈ D`;
4. `E' λ = E λ` for every `λ ∉ O`.

The neighbourhood `W` depends on `λ₀` only; `h` may depend on `g`. Clause 4
lets a consumer change `E` only inside a prescribed region `O` (for instance
to keep agreement with an Eisenstein series on a region of absolute
convergence disjoint from `O`). The universe-polymorphic theorem
`exists_isMeromorphicInCoordinatesOn_extension` has the same content for
`X : Type*`, `Γ : Type*`; the statement fixes universe `0`.

## Proof

- `isHolomorphicOn_iff_differentiableOn`: for scalar functions on `ℂⁿ`,
  `IsHolomorphicOn 𝓘(ℂ, Fin n → ℂ) f U` is `DifferentiableOn ℂ f U` (take
  `μ = id`; conversely compose with the continuous linear `μ`), via Mathlib's
  `mdifferentiableOn_iff_differentiableOn`.
- `IsMeromorphicOn.comp_continuousLinearEquiv_scalar`: meromorphy on `ℂⁿ` with domain
  `U` gives meromorphy of `f ∘ L` with domain `L⁻¹ U` for a continuous linear
  equivalence `L`: openness and density pull back along the homeomorphism
  `L`, and the local denominators `g`, `h` on a connected open `W` become
  `g ∘ L`, `h ∘ L` on `L⁻¹ W = L.symm '' W`.
- `isMeromorphicInCoordinatesOn_of_scalarCoordinates`: meromorphy in one linear
  coordinate system `e₀` implies it in every `e`, since
  `e₀⁻¹ ∘ e` is a linear isomorphism of finite-dimensional spaces, hence a
  continuous linear equivalence.
- `IsMeromorphicOn.of_extension`: if `f` is meromorphic with domain `U`,
  `U ⊆ U'` with `U'` open, and `f'` is differentiable on `U'` and equal to `f`
  on `U`, then `f'` is meromorphic with domain `U'`. The same local
  denominators work: `g • f' = h` holds on `U ∩ W` and both sides are
  continuous on the open set `U' ∩ W`, in which `U' ∩ W ∩ U` is dense
  (Mathlib's `Set.EqOn.of_subset_closure` and
  `Dense.open_subset_closure_inter`).
- `exists_differentiableOn_union_extension` (fixed coordinates): given `E · g`
  differentiable on a dense open `D` and functions `h i g` differentiable on
  open sets `W i` with `h i g = E · g` on `W i ∩ D`, put `E' s g = E s g` for
  `s ∈ D`, `E' s g = h i g s` for some (chosen) `i` with `s ∈ W i` if
  `s ∉ D`, and `E' s g = E s g` otherwise. Two extensions `h i g`, `h j g`
  agree on `W i ∩ W j` (continuity and density of `D`), so `E' · g = h i g` on
  all of `W i`; hence `E' · g` is differentiable at every point of the open
  set `D ∪ ⋃ i, W i`, equals `E` on `D`, and equals `E` outside `⋃ i, W i`.
- `exists_isMeromorphicInCoordinatesOn_extension`: if `Γ` is empty, take
  `E' = E`, `D' = univ`. Otherwise `X` is finite-dimensional; fix the
  coordinates `e₀` of `Module.finBasis`, transport every local datum
  `(e, W, h)` to `e₀` through `L = e⁻¹ ∘ e₀`, apply the fixed-coordinate
  gluing to `D₀ = e₀⁻¹ D` and the sets `L⁻¹ W`, and set `D' = e₀(D₀ ∪ ⋃ L⁻¹ W)`,
  `E' λ = E'₀ (e₀⁻¹ λ)`. Meromorphy of `E' · g` in the coordinates `e₀`
  follows from `IsMeromorphicOn.of_extension`, and in all coordinates from
  `isMeromorphicInCoordinatesOn_of_scalarCoordinates`. A point `λ ∉ O` lies in no
  `e₀(L⁻¹ W) = e(W) ⊆ O`, so `E' λ = E λ` there.

## Scope

The statement does not produce the local extensions; for Lapid's
Proposition 6 they come from the root-hyperplane description of the
singularities and the square-integrability argument, proved elsewhere.
