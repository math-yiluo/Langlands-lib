# The weighted Siegel Hilbert space on the adelic group

Module `Langlands.Global.AdelicLocalFinitenessSiegelFrame` (namespace
`Langlands.Global.WeightedSiegel`). It relates the weighted Hilbert spaces of the module
`Langlands.Global.AdelicWeightedSiegelSpace`, defined through the rational-parabolic quotient
`P(F) \ G(𝔸)`, to `L²` spaces on `G(𝔸)` for `W · Haar` on a fundamental domain, the setting of
the constant-term operators of `Langlands.Global.AdelicL2HarishChandraDecomposition`.

## Comparison of the two images of `P₀(F)`

- `parabolicPrincipalSubgroup_eq_minimalParabolicImage`: for a maximal split torus `i` and a
  generic cocharacter `ν`, the principal image `parabolicPrincipalSubgroup F p₀` of the
  rational points of the represented standard minimal parabolic
  `p₀ = Standard.parabolicHom i ν ∅` equals `StandardConstantTerm.minimalParabolicImage F G i ν`,
  the image of the rational points of the subgroup functor `standardParabolic i ν ∅`. Both are
  images of rational points of `G` lying in the range of `p₀`
  (`Standard.isRepresentedBy_parabolicHom`, `map_rational`).
- `fundamentalDomain_congr`: equal discrete subgroups have the same Library fundamental
  domain.

## The frame measure and the embedding

Fix a closed subgroup `p : P → G`, an Iwasawa compact `K` for `p` (`IsIwasawaCompact p K`), a
log weight `ell` on the real character dual of `P` and a set `S` of heights.

- `frameMeasure hK ell S` is `W · Haar` restricted to the fundamental domain of
  `parabolicPrincipalSubgroup F p`, where `W = chamberDensity F p hK ell S` is
  `exp(-2 ell(H_P(g)))` on `H_P⁻¹(S)` and zero elsewhere.
- `map_mk_frameMeasure` (for continuous `ell` and Borel `S`): the quotient map
  `G(𝔸) → P(F) \ G(𝔸)` pushes `frameMeasure hK ell S` forward to
  `domainMeasure F p hK ell (H_P⁻¹(S))`. On a measurable set this is the identity
  `lintegral_domainMeasure_eq_chamberDensity` applied to its indicator.
  `measurePreserving_mk_frameMeasure` restates it.
- `frameEmbedding hK ell hell S hS` is the linear isometry from
  `HilbertSpace F p hK ell (H_P⁻¹(S))` (`L²` of `G(F) \ G(𝔸)` for the pushforward of the
  weighted domain measure) into `Lp ℂ 2 (frameMeasure hK ell S)`: the isometric `pullback` to
  the rational-parabolic quotient followed by composition with the measure-preserving
  quotient map. `frameEmbedding_ae`: on representatives it is composition with the quotient
  map `G(𝔸) → G(F) \ G(𝔸)`.
- `frameMeasure_eq_standard`: for `p = p₀`, the frame measure is `W · Haar` on the fundamental
  domain of `minimalParabolicImage F G i ν`, the measure used by the standard constant-term
  operators.

## Provenance

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc.
37 (2024), 187–234, §7.4, p. 215 (literature id
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`): the space `H^λ(X)` consists of
functions on `G(F) \ G(𝔸)` whose pullback to the Siegel domain lies in
`L²(𝔖, w_λ⁻² dx)`. This module realizes that norm on `G(𝔸)` through a fundamental domain of
`P₀(F)`, so that the Harish-Chandra decomposition of §7.3 can be applied to the pullback. It is
derived infrastructure; it proves no estimate of BL.
