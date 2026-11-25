# Meromorphic functions with values in a space of functions with pointwise convergence

Module `Langlands.Analysis.Meromorphic.PointwiseValues`, written for the meromorphic
continuation of intertwining operators in the topology of pointwise convergence
(`IntertwiningWeakMeromorphicContinuationStatement`, Bernstein–Lapid §8.5). All declarations are in the namespace
`Langlands.Analysis.Meromorphic`. The module is generic: it does not mention groups or
automorphic forms.

## Context

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37
(2024), §3.1, p. 192 (registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`).
There, holomorphy and meromorphy of functions with values in a locally convex space are defined
by testing against continuous linear forms, with one local scalar denominator for the whole
vector-valued function. The Library formalizes these notions as `IsHolomorphicOn` and
`IsMeromorphicOn` (module `Langlands.Analysis.Meromorphic.AnalyticSystems`). This module treats
the case where the values lie in the product `ι → ℂ` with Mathlib's product topology (the
topology of pointwise convergence). That case is used for functions on `G(𝔸)` in
`Langlands.Global.AdelicIntertwiningWeakContinuationReduction`. These are internal lemmas; BL
state none of them.

## Declarations

- `exists_finset_continuousLinearMap_pi_eq_sum`: every continuous `ℂ`-linear form `μ` on
  `ι → ℂ` has a finite set `S` with `μ x = ∑ i ∈ S, x i * μ (Pi.single i 1)` for all `x`.
  *Proof.* `Langlands.Analysis.continuousLinearMap_product_factors`, applied to `μ` as a real
  linear map, shows that `μ x` depends only on the coordinates of `x` in a finite set `S`. The
  vector `∑ i ∈ S, x i • Pi.single i 1` has the same coordinates on `S`. So `μ` takes the same
  value on it, and complex linearity gives the sum.
- `isHolomorphicOn_pi_of_differentiableOn`: a function `f : ℂᵐ → (ι → ℂ)` whose coordinates
  `s ↦ f s i` are complex differentiable on `U` satisfies `IsHolomorphicOn` on `U`. Each
  `μ ∘ f` is a finite sum of coordinates times constants by the previous lemma.
- `differentiableOn_apply_of_isHolomorphicOn`: the converse for each coordinate. Use the
  coordinate projection as `μ`.
- `exists_isMeromorphicOn_pi_of_local`: let `φ i`, `i ∈ ι`, be scalar functions on `ℂᵐ` with
  `HasLocalMeromorphicData φ s₀` at every `s₀` (module `CoordinateGluing`). In that predicate
  the local denominator does not depend on `i`. Then some `U` satisfies
  `IsMeromorphicOn 𝓘(ℂ, Fin m → ℂ) (fun s i => φ i s) U`. The values lie in `ι → ℂ`.
  *Proof.* This repeats the proof of `exists_isMeromorphicOn_of_local` in `CoordinateGluing`
  with the same `U`: the points with an open neighbourhood on which every `φ i` is
  differentiable. `U` is open. It is dense because every local domain is contained in `U` and
  its closure contains the local neighbourhood. The function-valued numerator is
  `s ↦ (h i s)ᵢ`, where `h i` are the local numerators. The previous lemma makes it holomorphic.
  The identity `q s • f s = h s` on `U ∩ W` is proved coordinatewise. Both sides are continuous
  on `U ∩ W` and agree on the dense subset `D ∩ W`, so they agree on `U ∩ W`.
- `exists_ne_zero_of_differentiable`: an entire function on `ℂᵐ` that is nonzero at one point
  is nonzero somewhere in every nonempty open set. This is the identity theorem
  `exists_ne_zero_of_differentiableOn` of `ContinuationUniqueness`, applied with `W = ℂᵐ`.
- `HasLocalMeromorphicData.combination`: let `φ` have local data at `s₀`. Let `den` be entire
  with `den s₁ ≠ 0` for some `s₁`. Suppose
  `Ψ x s = (den s)⁻¹ * ∑ k ∈ Finset.range B, coef x k s * φ (idx x k) s` with entire
  coefficients `coef x k`. Then `Ψ` has local data at `s₀`.
  *Proof.* The new domain is `D ∩ {den ≠ 0}`. It is open, and `Ψ x` is differentiable on it.
  The set `{den ≠ 0}` is open and dense by the previous lemma, so the neighbourhood `W` stays in
  the closure of the new domain (`Dense.open_subset_closure_inter`). The new denominator is
  `q * den`. It is differentiable on `W`. It is nonzero somewhere on `W`: `q` is nonzero on a
  nonempty open subset of `W`, and `den` is nonzero at some point of that subset. The new
  numerators are `∑ k, coef x k * h (idx x k)`. On `D ∩ {den ≠ 0} ∩ W` the identity follows from
  `q φ_i = h_i` by cancelling `den`.

## Scope

All results are about functions on `ℂᵐ` (`Fin m → ℂ`). The passage to an arbitrary
finite-dimensional complex vector space with all linear coordinate systems is done elsewhere,
with `isMeromorphicInCoordinatesOn_of_coordinates` of `CoordinateGluing`. Axioms used:
`propext`, `Classical.choice`, `Quot.sound`.
