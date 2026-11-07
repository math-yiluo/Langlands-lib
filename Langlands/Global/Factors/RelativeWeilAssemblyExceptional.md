# Exceptional places in the assembly of the relative Weil functional equation

## Contents

This module supports the proof of
`Langlands.Global.FunctionalEquationComparison.RelativeWeilTwistFunctionalEquationStatement`.
That statement fixes a finite set `T₀` of finite places before the twisting character `χ`.
This module provides the facts needed to choose `T₀` and to treat the places outside an
exceptional set `B ⊇ T₀`. They are: vanishing of additive conductors outside a finite set,
`ε = 1` at unramified places of conductor zero, and the analytic behaviour of the Hecke
L-factors and of epsilon monomials. The Hecke global functional equation
(`HeckeGlobalFunctionalEquationStatement`) is an explicit hypothesis `hH` of the one result that
uses it and is not proved here. All names are in namespace
`Langlands.Global.FunctionalEquationComparison.RelativeWeilEngine`.

### Local

For a `p`-adic field with topological data `T`:

- `additiveConductor_eq_zero_of_epsilon_eq_one`: let `χ` be a quasicharacter with
  multiplicative conductor `0`, `ψ` an additive character and `μ` a Borel measure. If the
  published epsilon expression `LocalFactor.PadicAbelian.epsilon T χ ψ μ s` equals `1` at
  `s = 0` and at `s = 1`, then the additive conductor of `ψ` is `0`.

### Hecke characters of a number field `K`

- `isUnramifiedAt_one`, `isUnramifiedAt_mul`: the trivial Hecke character is unramified
  everywhere, and a product of characters unramified at `v` is unramified at `v`.
- `eq_of_isFiniteAdditiveComponent`: two finite additive components (in the sense of the
  published `HeckeFunctionalEquation.IsFiniteAdditiveComponent`) of the same adelic character
  at the same place are equal.
- `additiveConductor_eq_zero_of_finiteEpsilon`: if `χ` is unramified at `v` and the finite
  epsilon factor `HeckeFunctionalEquation.finiteEpsilon χ ψf μ v s` is `1` for all `s`, then
  the additive conductor of `ψf v` is `0`.
- `finiteEpsilon_eq_one`: if `χ` is unramified at `v` and `ψf v` has additive conductor `0`,
  then `finiteEpsilon χ ψf μ v s = 1` for every `s`.
- `exists_finset_additiveConductor_eq_zero` (hypothesis `hH`): let `ψ` be a nontrivial
  character of `A_K` trivial on `K`, and `ψf` a family of finite components of `ψ` at all
  finite places. Then the additive conductor of `ψf v` is `0` for `v` outside a finite set.
- `nonzeroConductorPlaces ψf` (definition): for a family `ψf` of additive characters of the
  completions `K_v` at the finite places, the set of finite places `v` at which `ψf v` has
  nonzero additive conductor (`TopologicalData.additiveConductor`).
- `finite_nonzeroConductorPlaces` (hypothesis `hH`): under the hypotheses of
  `exists_finset_additiveConductor_eq_zero`, the set `nonzeroConductorPlaces ψf` is finite.
- `heckeL_eq`: `heckeL χ v s = (1 - a_v(s))⁻¹`, where `a_v(s)` is the published coefficient
  `HeckeEulerProduct.coeff χ v s`. It is `χ_v(ϖ_v) q_v^{-s}` if `χ` is unramified at `v`,
  and `0` otherwise.
- `exists_heckeL_ne_zero`: there is `σ₀` such that `heckeL χ v s ≠ 0` for every finite place
  `v` and every `s` with `σ₀ < Re s`.
- `differentiable_coeff`, `nonzeroMeromorphic_heckeL`: `a_v` is entire, and `heckeL χ v` has
  nonzero germ at every point.

### Germs

- `nonzeroMeromorphic_epsilonMonomial`: for `q > 0`, the published epsilon monomial
  `RankinSelberg.epsilonMonomial q c m`, `s ↦ c · q^{-ms}`, has nonzero germ at every point.
- `meromorphicEq_of_eq_of_ne_zero`: if `f s = g s` whenever `G s ≠ 0`, and `G` has nonzero germ
  everywhere, then `f` and `g` have the same germ on every punctured neighbourhood
  (`MeromorphicEq f g`).

## Source and provenance

John Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33, Part II (1979), 3–26
(registered `tate-1979-number-theoretic-background`). Formula (3.2.6.1), printed p.13 (PDF
p.22), gives the unramified local constant `ε(χ, ψ, dx) = χ(c) ‖c‖⁻¹ ∫_O dx`, where `c` has
valuation `n(ψ)`, the largest `n` with `ψ(ϖ^{-n} O) = 1`. For `χ ω_s` this is
`χ(ϖ)^{n(ψ)} q^{n(ψ)(1-s)} ∫_O dx`. The published `PadicAbelian.epsilon` is this expression at
multiplicative conductor `0`. `additiveConductor_eq_zero_of_epsilon_eq_one` reads `n(ψ) = 0`
off its values at `s = 0` and `s = 1`. The global epsilon factor (3.5.2), printed p.16 (PDF
p.25), is a product over all places, so almost all local constants are `1`.

The route through the Hecke functional equation of the trivial character is internal. The
Hecke statement gives `ε_v = 1` outside a finite set, and the previous lemma turns this into
vanishing of the additive conductors there. This avoids adelic self-duality, which is
available in the Library only as the unproved `AdelicAdditiveDualityStatement`. The other
results are internal bookkeeping on published definitions.

## Proof

- `additiveConductor_eq_zero_of_epsilon_eq_one`: at multiplicative conductor `0`, the epsilon
  expression is `χ(ϖ)^n · exp(n(1 - s) log q) · vol`. At `s = 1` this gives
  `χ(ϖ)^n · vol = 1`. At `s = 0` it then gives `exp(n log q) = 1`, so `n · log q = 0`.
  Since `q > 1` (`residueCardinality_gt_one`), `log q > 0`, and `n = 0`.
- `eq_of_isFiniteAdditiveComponent`: both components have the values of `ψ` on the image of
  the local field, so their underlying additive characters agree, and the remaining fields are
  propositions.
- `additiveConductor_eq_zero_of_finiteEpsilon` applies the local lemma to the component
  `χ_v`, which has conductor `0` by the published `multiplicativeConductor_eq_zero_of_isUnramifiedAt`.
  `finiteEpsilon_eq_one` is the published `epsilon_eq_one_of_conductors_eq_zero`.
- `exists_finset_additiveConductor_eq_zero`: choose self-dual measures
  (`nonempty_selfDualHaar`) and archimedean data for the trivial character
  (`nonempty_heckeArchData`). `hasGlobalEquation_of_heckeArchData` then gives a finite set `S`
  outside which the finite epsilon factors of the trivial character are `1`. Apply
  `additiveConductor_eq_zero_of_finiteEpsilon` at every `v ∉ S`.
  `finite_nonzeroConductorPlaces`: the set is contained in that finite set `S`.
- `heckeL_eq` is the published `HeckeEulerProduct.lFactor_eq`.
- `exists_heckeL_ne_zero`: by the published `exists_norm_finiteComponent_uniformizer` and
  `norm_coeff_le`, `‖a_v(s)‖ ≤ N(v)^{-(β + Re s)}` for some `β`. Take `σ₀ = -β`. Then
  `‖a_v(s)‖ < 1` since `N(v) > 1`, so `1 - a_v(s) ≠ 0`.
- `differentiable_coeff`: `a_v` is a constant times an exponential, or `0`.
  `nonzeroMeromorphic_heckeL`: `(1 - a_v)⁻¹` is meromorphic as the inverse of an entire
  function. It is nonzero on the half-plane of `exists_heckeL_ne_zero`, so
  `nonzeroMeromorphic_of_ne_zero_halfPlane` applies.
- `nonzeroMeromorphic_epsilonMonomial`: `c · (q^{-s})^m` is entire, since `q^{-s}` is
  differentiable and nonzero. It is nowhere zero by the published `epsilonMonomial_ne_zero`.
- `meromorphicEq_of_eq_of_ne_zero`: `G` is nonzero on a punctured neighbourhood of every point
  (`NonzeroMeromorphic.eventually_ne_zero`), and there `f = g`.
