# Whittaker completeness: orthogonality to a representation

This supporting module is a helper for the proof of
`Langlands.Whittaker.WhittakerCompletenessStatement` (Jacquet and Shalika 1985,
Lemma 3.2). That proof reduces the statement to the published proposition
`Langlands.RankinSelberg.SupercuspidalProductCompletenessStatement`. It applies
that proposition with the character `ψ⁻¹ = ψ.scale (-1)`, and deforms test
representations through a real twisting parameter. This module introduces the
orthogonality predicate used along the way. It proves the predicate's formal
properties, the change of character, and the deformation step. It states and
proves no result from the literature.

## The orthogonality predicate

Let `F` be a field with a topology, `ψ` a unitary additive character, `μ` a
measure on `N \ GL_(n+1)(F)` and `H` a standard-character function
(`WhittakerFunctions ψ n`).

- `Orthogonal ψ μ H π` (the module's only definition) says that
  `∫ whittakerProductIntegrand ψ H f dμ = 0` for every `f` in
  `inverseWhittakerSet ψ n π`. That set contains the inverse-character Whittaker
  functions `g ↦ ℓ'(π(g) v)` of `π`, over all inverse-character Whittaker
  functionals `ℓ'` and vectors `v`.
- `orthogonal_iff_forall_coefficientModel`: `Orthogonal ψ μ H π` holds if and
  only if the pairing vanishes for every `ℓ' : glInverseFunctionals ψ n π` and
  every `f` in `coefficientModel π ℓ'`. This is the form of the hypothesis of
  `SupercuspidalProductCompletenessStatement`, for one representation.
- `Orthogonal.of_surjective`: orthogonality to `π` implies orthogonality to every
  quotient `π₂`, given a surjective intertwining map `π → π₂`.
- `orthogonal_iff_of_equiv`: equivalent representations, possibly with carriers in
  different universes, have the same orthogonal functions.
- `whittakerProductIntegrand_zero`: the integrand of the pairing with the zero
  function is zero.

## Change of character

Over a topological ring `F`, the published adapters
`InducedTailIntermediate.inverseAsScaledStandard` and `scaledInverseAsStandard`
reread an inverse-character function for `ψ` as a standard-character function for
`ψ.scale (-1)`, and an inverse-character function for `ψ.scale (-1)` as a
standard-character function for `ψ`. Neither changes the underlying function.

- `whittakerProductIntegrand_scale_neg_one`: the integrand of `∫ W H` for `ψ`
  equals the integrand of `∫ H W` for `ψ.scale (-1)`, the factors being
  exchanged.
- `isCompactWhittakerTestFunction_inverseAsScaledStandard`: an inverse-character
  function `H` for `ψ` satisfies the invariance and support hypotheses of the
  target statement. Then `inverseAsScaledStandard ψ H` is a compact Whittaker
  test function (`IsCompactWhittakerTestFunction`) for `ψ.scale (-1)`.
- `orthogonal_scale_neg_one_of_forall`: suppose `∫ W H dμ = 0` for every standard
  Whittaker function `W` of `π` for `ψ`, that is, for every `W` in a coefficient
  model of a functional in `glFunctionals ψ n π`. Then
  `Orthogonal (ψ.scale (-1)) μ (inverseAsScaledStandard ψ H) π`. Each
  inverse-character function for `ψ.scale (-1)` of `π` is a standard Whittaker
  function for `ψ` (`scaledInverseAsStandard_mem`), and the integrands agree.

## Over a p-adic field

Let `F` be a p-adic field with its canonical structures.

- `orthogonal_scale_neg_one_of_isGeneric`: assume the hypothesis of the target
  statement for carriers in `Type uV`. That is, `∫ W H dμ = 0` for every standard
  Whittaker function `W` of every generic representation on a carrier in
  `Type uV`. Then `inverseAsScaledStandard ψ H` is orthogonal at `ψ.scale (-1)`
  to every generic representation, with carrier in any universe. The proof
  combines `orthogonal_scale_neg_one_of_forall` with the published universe
  transport `forall_coefficientModel_of_isGeneric`.
- `orthogonal_twoBlockDeformedInduced_zero`, the deformation step. Let `σ 0`,
  `σ 1` be representations of Whittaker type for the standard character, and let
  `twoBlockDeformedInduced F m h σ u` be the published canonical normalized
  lower parabolic induction of the blocks `σ 0 ⊗ |det|^u` and `σ 1 ⊗ |det|^0`. Let `H` be a compact Whittaker test function and `μ`
  a measure finite on compact sets with open sets measurable. If `H` is
  orthogonal to `twoBlockDeformedInduced F m h σ (u : ℂ)` for all real `u ≠ 0`
  near `0` (eventually along `𝓝[≠] 0`), then `H` is orthogonal to
  `twoBlockDeformedInduced F m h σ 0`.

The proof of the deformation step runs as follows. Take a Whittaker function
`g ↦ ℓ₀(ρ_0(g) v₀)` of `ρ_0`. If `ℓ₀ = 0` it is zero and its pairing is zero.
Otherwise the published `twoBlockWhittakerDeformation` gives the following data
for every complex `u`: functionals `ℓ_u`, vectors `v_u` and functions
`W_u(g) = ℓ_u(ρ_u(g) v_u)`. The family satisfies `W_0 = ℓ₀(ρ_0(·) v₀)`, every
`W_u` is right invariant under one open subgroup `K`, and `u ↦ W_u(g)` is
analytic for every `g`. Restricting to real `u`, `W_u(g) → W_0(g)` along
`𝓝[≠] 0`. The pairing with each `W_u`, `u ≠ 0` near `0`, vanishes by hypothesis,
so `integral_whittakerProductIntegrand_eq_zero_of_tendsto`
(`CompletenessPairing`) gives the vanishing of the pairing with `W_0`.

## Provenance

The module is internal. It was written for the proof of
`WhittakerCompletenessStatement`, whose reduction to products of supercuspidals
follows the deformation argument of Jacquet, Piatetski-Shapiro and Shalika 1983,
Section (4.5). The deformation of Whittaker functions itself is the published
`twoBlockWhittakerDeformation`. The statements here are formal consequences of
published Library results, and none is attributed to a source.

Integration uses module-specific names for local instances. Their types, values,
and local instance scopes are unchanged.
