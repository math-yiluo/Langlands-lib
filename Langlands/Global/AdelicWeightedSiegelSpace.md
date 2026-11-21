# Weighted Hilbert spaces from an adelic Siegel domain

`Langlands.Global.WeightedSiegel` constructs the fixed-domain weighted
Hilbert stage of Bernstein–Lapid §§7.3–7.4. It works for a supplied closed
immersion `p : P → G` over a number field, a supplied Iwasawa compact `K`
for `p`, a domain `S` in the rational-parabolic quotient, and a scalar
function `ell` on the real character dual of `P`. The intended `P` is
the minimal parabolic `P₀`. No existence or reduction theorem for `K`
or `S` is assumed to follow from this module.

## Quotients and measures

- `parabolicPrincipalSubgroup` is the image of `P(F)` in `G(𝔸)`, by
  functoriality of the principal map. It is a subgroup of the discrete
  principal subgroup of `G`, hence discrete. `DomainQuotient` is the
  actual left quotient `P(F) \ G(𝔸)`, and `domainHaarMeasure` is the
  Haar quotient by this discrete subgroup, with the counting convention
  of `LeftCosetSpace.haarQuotientMeasure`. The map `toAutomorphic` is the
  continuous quotient projection to `G(F) \ G(𝔸)`.
- `domainHeight` is the Iwasawa height `hK.height` on representatives.
  It is invariant under `P(F)` by the product-formula identity
  `height_rational_mul`, so it descends to `DomainQuotient`. Its continuity
  (`continuous_domainHeight`) is the descent through the quotient topology
  of the published `IsIwasawaCompact.continuous_height` (module
  `Langlands.Global.AdelicEisensteinCompactBounds`), continuity into the
  character dual with the topology of pointwise character evaluations.
  This module reuses that theorem and does not restate it.
- `domainMeasure` restricts `domainHaarMeasure` to `S` and applies density
  `exp(-2 ell(H_P))`, using the measured ambient quotient rather than a
  subtype on points. This is `w⁻²` for `w = exp(ell(H_P))`. The density
  is measurable when `ell` is continuous; the interface allows more than
  linear functions, to include continuous piecewise-linear weights in
  the central directions.
- `automorphicMeasure` is the **pushforward** of `domainMeasure` along
  `toAutomorphic`. Thus the definition implements the induced norm from
  the weighted domain, without assuming a section or estimating fibre
  multiplicity. `HilbertSpace` is the actual complex `Lp` at exponent two
  for that pushforward measure. `pullback` is the linear isometry
  `Lp.compMeasurePreservingₗᵢ`, with composition on representatives
  (`pullback_ae`). For strongly measurable functions `memLp_iff_pullback`
  identifies membership in the pushforward Hilbert stage with membership
  of the pulled-back function in the weighted domain stage.

## Provenance and limitations

Joseph Bernstein and Erez Lapid, *On the meromorphic continuation of
Eisenstein series*, J. Amer. Math. Soc. 37 (2024), 187–234, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §7.3 (pp.214–215,
`Z` and the exponential weights) and §7.4 (pp.215–216, induced Hilbert
norm), with the central orthants of §7.7 (pp.220–221). The pushforward is a
realization of the norm pulled back from one supplied domain; it does not
prove equivalence between domains, comparison with a weighted ambient
automorphic Haar measure, boundedness of right translation/convolution,
or that a suitable domain is available for every group in Theorem 7.2.
The relative quotients `Z_P`, constant-term projections, solution lifts,
and smoothing operators are also not constructed here.
