# Identity theorems for holomorphic and meromorphic functions of several variables

Module `Langlands.Analysis.Meromorphic.IdentityTheorem` proves identity
theorems for scalar functions `f : E → ℂ` on a complex normed space `E` (in
the applications `E = ℂⁿ`), for complex differentiable functions and for
meromorphic functions in the sense of
`Langlands.Analysis.Meromorphic.IsMeromorphicOn` (module
`Langlands.Analysis.Meromorphic.AnalyticSystems`, Bernstein–Lapid §3.1). It
also proves closure properties of scalar meromorphic functions. It defines
nothing. All declarations are in the namespace
`Langlands.Analysis.Meromorphic`.

These are standard facts of complex analysis in several variables. Mathlib
has the identity theorem for analytic functions, but it proves analyticity of
complex differentiable functions only in one variable. So the proofs here
restrict to complex lines.

## Holomorphic functions

- `eqOn_zero_of_convex_of_eventuallyEq_zero`: a function complex
  differentiable on a convex open set `U` that vanishes near a point `y ∈ U`
  vanishes on `U`. For `z ∈ U`, the function `t ↦ f(y + t(z - y))` is complex
  differentiable on the convex open set `{t | y + t(z - y) ∈ U} ⊆ ℂ`, hence
  analytic there (Mathlib, one variable). It vanishes near `0`, so by
  Mathlib's identity theorem for analytic functions it vanishes at `1`.
- `eqOn_zero_of_isPreconnected_of_eventuallyEq_zero`: the same on a
  preconnected open set. The set of points near which `f` vanishes is open.
  It is relatively closed in `U` by the convex case applied to balls, so it
  contains `U` by preconnectedness.
- `eqOn_of_isPreconnected_of_eventuallyEq`: two such functions that agree
  near a point agree on `U`.
- `exists_ne_zero_of_isOpen_subset`, `subset_closure_inter_ne_zero`,
  `exists_mul_ne_zero_of_isOpen_subset`: a function complex differentiable on
  a preconnected open set `W` and not identically zero there is not
  identically zero on any nonempty open subset of `W`. Its nonvanishing set is
  dense in every open subset of `W`, and a product of two such functions is
  not identically zero on a nonempty open subset of both domains.

## Scalar meromorphic functions

- `isHolomorphicOn_iff_differentiableOn_scalar`: for scalar functions on `E`, the
  weak holomorphy `IsHolomorphicOn 𝓘(ℂ, E)` (holomorphy of `μ ∘ f` for
  every continuous linear functional `μ`) is complex differentiability.
- `isMeromorphicOn_iff`: the definition of `IsMeromorphicOn 𝓘(ℂ, E) f U` for
  scalar `f` in these terms. `U` is open and dense, `f` is complex
  differentiable on `U`, and every point has a connected open neighbourhood
  `W` with functions `g`, `h` complex differentiable on `W`, `g` not
  identically zero on `W`, and `g · f = h` on `U ∩ W`.
- `isMeromorphicOn_zero_of_isOpen_dense`, `IsMeromorphicOn.add_sameDomain`,
  `IsMeromorphicOn.mul_const`, `isMeromorphicOn_sum`: zero, sums, constant
  multiples and finite sums of meromorphic functions with one domain `U` are
  meromorphic with domain `U`. For a sum, the local presentations `g₁ f₁ = h₁`
  and `g₂ f₂ = h₂` give `g₁ g₂ (f₁ + f₂) = g₂ h₁ + g₁ h₂` on a ball inside both
  neighbourhoods. `g₁ g₂` is not identically zero on the ball by the previous
  section.
- `IsMeromorphicOn.eq_of_eqOn_isOpen` (**identity theorem for meromorphic
  functions**): if `f₁` and `f₂` are meromorphic with domains `U₁` and `U₂` and
  agree on `V ∩ U₁ ∩ U₂` for a nonempty open `V`, they agree on `U₁ ∩ U₂`. The
  set of points near which `f₁ = f₂` on `U₁ ∩ U₂` is open and nonempty. It is
  closed: near a point `x` of its closure take a ball `B` inside the
  neighbourhoods of both local presentations. The function
  `H = g₂ h₁ - g₁ h₂` is complex differentiable on `B` and equals
  `g₁ g₂ (f₁ - f₂)` on `B ∩ U₁ ∩ U₂`. It vanishes on an open subset of `B`
  near a point of the set (by density of `U₁ ∩ U₂` and continuity), hence on
  `B`. So `f₁ = f₂` where `g₁ g₂ ≠ 0`, a dense subset of `B ∩ U₁ ∩ U₂`, and by
  continuity on all of `B ∩ U₁ ∩ U₂`. Since `E` is connected, the set is
  everything.
- `IsMeromorphicOn.eq_mul_of_eqOn_isOpen` (**transfer of a cleared form**):
  with `f₁`, `f₂`, `V` as above, if `h` is continuous on an open `W` and
  `h = p · f₂` on `W ∩ U₂` for a continuous `p`, then `h = p · f₁` on
  `W ∩ U₁`. Both sides agree on `W ∩ U₁ ∩ U₂` by the identity theorem, which
  is dense in `W ∩ U₁` because `U₂` is open and dense, and both are continuous
  on `W ∩ U₁`.

## Use

The transfer lemma is the analytic step of
`Langlands.Global.AdelicRootHyperplaneReduction`. It moves the root-hyperplane
product form from one continuation of an intertwining operator or Eisenstein
series to any other continuation that agrees with it on a nonempty open set of
regular parameters.
