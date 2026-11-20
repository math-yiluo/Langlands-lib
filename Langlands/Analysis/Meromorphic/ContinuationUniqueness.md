# Uniqueness of meromorphic continuation in linear coordinates

Module `Langlands.Analysis.Meromorphic.ContinuationUniqueness` proves that a
meromorphic continuation is unique. It covers meromorphic functions in the
sense of `IsMeromorphicOn` (module
`Langlands.Analysis.Meromorphic.AnalyticSystems`) on open subsets of `ℂⁿ`,
even when they are written in two different linear coordinate systems of
one complex vector space. The meromorphic continuation of Eisenstein series
glues continuations obtained on different bounded parameter sets. This
module supplies the comparison it needs.

## Provenance

Internal. These are standard facts of several complex variables: the
identity theorem, and its consequence that meromorphic functions agreeing
on a nonempty open set agree wherever both are holomorphic. Mathlib has the
identity theorem only for functions of one complex variable
(`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` together
with `DifferentiableOn.analyticOnNhd`). The several-variable version here is
proved by restricting to complex lines.

Bernstein–Lapid (registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §3.1, journal
p.192) define meromorphic functions through local scalar denominators. The
Library's `IsMeromorphicOn` formalizes that definition. Its holomorphy is weak
holomorphy: `IsHolomorphicOn` tests every continuous linear form.

## Results in a complex normed space `E`

- `eqOn_zero_of_differentiableOn_of_eventuallyEq_zero`: the identity
  theorem. Let `ψ : E → ℂ` be complex differentiable on a connected open set
  `W` and vanish near one point of `W`. Then it vanishes on `W`.
  Proof: the set of points near which `ψ` vanishes is open. It is also
  closed in `W`. Indeed, if `t ∈ W` is in its closure, pick a ball around `t`
  inside `W` and a point `t'` of the set in that ball. For each `y` in the
  ball, the line `z ↦ t' + z (y - t')` meets the ball in a convex open set of
  `ℂ` containing `0` and `1`, and the one-variable identity theorem gives
  `ψ(y) = 0`. Connectedness of `W` concludes.
- `exists_ne_zero_of_differentiableOn`: a function as above that is not
  identically zero on `W` is nonzero somewhere on every nonempty open subset
  of `W`.
- `HasLocalDenominators Φ D Ω` (a predicate): every point of `Ω` has a
  connected open neighborhood `W` with `g`, `h : E → ℂ` complex
  differentiable on `W`, `g` not identically zero on `W`, and `g Φ = h` on
  `D ∩ W`. It is the flat, scalar form of the denominator clause of
  `IsMeromorphicOn`. Lemmas: `HasLocalDenominators.mono` (shrinking `Ω`) and
  `HasLocalDenominators.comp` (pulling back along a continuous linear
  equivalence).
- `nonempty_inter_inter_of_subset_closure`: if `Ω` is open, `D₁` is open,
  and `D₁` and `D₂` are both dense in `Ω`, then every open set meeting `Ω`
  meets `D₁ ∩ D₂`.
- `eq_of_hasLocalDenominators`: uniqueness of meromorphic continuation.
  Let `Ω` be a connected open set. Let `Φ₁`, `Φ₂` be continuous on open sets
  `D₁`, `D₂` dense in `Ω`, with local denominators at every point of `Ω`.
  Suppose `Φ₁ = Φ₂` on `D₁ ∩ D₂` near one point of `Ω`. Then `Φ₁ = Φ₂` on
  all of `Ω ∩ D₁ ∩ D₂`.
  Proof: the set of points near which the agreement holds is open; it is
  closed in `Ω` by the following argument. Near a limit point `t`, take
  denominators `g₁ Φ₁ = h₁` and `g₂ Φ₂ = h₂` on a common ball. Then
  `g₂ h₁ - g₁ h₂` is holomorphic on the ball and vanishes on a nonempty open
  subset (by continuity and density), so it vanishes on the ball by the
  identity theorem. If `Φ₁(y) ≠ Φ₂(y)` at some `y` of the ball, then near
  `y` we can find a point of `D₁ ∩ D₂` where `g₁`, `g₂` and `Φ₁ - Φ₂` are all
  nonzero (by `exists_ne_zero_of_differentiableOn` twice), a contradiction.

## Passing from open subsets to flat functions

- `extendOpens f`: for an open set `B ⊆ E` and `f : B → β`, the function on
  `E` equal to `f` on `B` and to `0` elsewhere. `extendOpens_coe` states
  that it restricts to `f`.
- `differentiableOn_extendOpens`: if `f : B → ℂ` is complex differentiable
  (in the manifold sense, for the open-subset structure of `B`) on an open
  `S ⊆ B`, then `extendOpens f` is complex differentiable on the image of
  `S` in `E`.
- `IsMeromorphicOn.flat`: let `v : B → V` be meromorphic with domain of
  holomorphy `U`, and `μ` a continuous linear form on `V`. Then the image of
  `U` in `E` is open and dense in `B`. The function `extendOpens (μ ∘ v)` is
  complex differentiable on that image and has local denominators at every
  point of `B`.

## Comparison across coordinate systems

`IsMeromorphicOn.eq_of_linearCoordinates`. Let `X` be a complex vector space
with linear coordinate systems `e₁ : ℂ^{n₁} ≃ X` and `e₂ : ℂ^{n₂} ≃ X`. Let
`A ⊆ X` be nonempty with `e₁⁻¹(A)` open. Let `B₁ ⊆ ℂ^{n₁}` and
`B₂ ⊆ ℂ^{n₂}` be convex open sets with `e₁⁻¹(A) ⊆ B₁` and `e₂⁻¹(A) ⊆ B₂`.
Let `v₁ : B₁ → V₁` and `v₂ : B₂ → V₂` be meromorphic with domains of
holomorphy `U₁`, `U₂`. Let `μ₁`, `μ₂` be continuous linear forms on `V₁`,
`V₂`, and `ψ : X → ℂ` a function. Assume `μ₁(v₁ s) = ψ(e₁ s)` for
`s ∈ U₁` with `e₁ s ∈ A`, and the same for the second system. Then
`μ₁(v₁ s₁) = μ₂(v₂ s₂)` whenever `s₁ ∈ U₁`, `s₂ ∈ U₂` and `e₁ s₁ = e₂ s₂`.

Proof: transport the second system to the first coordinates through the
continuous linear equivalence `T = e₂⁻¹ ∘ e₁`. Apply
`eq_of_hasLocalDenominators` on the convex, hence connected, open set
`Ω = B₁ ∩ T⁻¹(B₂)`, which contains `e₁⁻¹(A)`. The two functions agree near
any point of `e₁⁻¹(A)`, since there both equal `ψ ∘ e₁` where both are
holomorphic.

Note that `A` itself need not be open in `X`. `X` carries no topology here,
and only `e₁⁻¹(A)` must be open. Since `T` is a homeomorphism, `e₂⁻¹(A)` is
then open too.
