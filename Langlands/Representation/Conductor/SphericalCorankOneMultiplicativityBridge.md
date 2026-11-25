# The multiplicativity input of the corank-one reduction

Module `Langlands.Representation.Conductor.SphericalCorankOneMultiplicativityBridge`
(part of the proof of `SphericalCorankOneFunctionalEquationStatement`).

## Inputs

- `LocalFieldPrincipalSeriesGammaMultiplicativityStatement` (published statement, JPSS
  1983, Theorem (3.1)(i), for `π × I(z)` over every nonarchimedean local field). It is a
  hypothesis of the theorem below.
- `isGeneralPairGammaFactor_unramifiedTest` (published theorem, module
  `Langlands.Representation.RankinSelberg.LocalFieldUnramifiedTestTwist`). Let `F` have
  residue cardinality `q > 1`, uniformizer `ϖ`, and an absolute value `abv` with
  `abv ϖ = q⁻¹` and `abv u = 1` on valuation units. If `G` is the gamma factor of `π × 1`
  (`IsGeneralPairGammaFactor`, trivial rank-one test), then for every `z : ℂˣ` the rescaled
  function `G(zX)` (`rationalRescale z G`) is the gamma factor of `π × χ_z`. Here `χ_z` is
  the unramified character with `χ_z(ϖ) = z` (`UnramifiedPrincipalSeries.character`).

## Theorem `principalSeriesGammaInput_of_multiplicativity`

`PrincipalSeriesGammaInput` (from `SphericalCorankOneReduction`) follows from
`LocalFieldPrincipalSeriesGammaMultiplicativityStatement`; the twist identity is proved.

Proof as implemented:
1. A generic `π` is of Whittaker type (`isOfWhittakerType_of_isGeneric_localField`).
2. Every measurable structure in the context is Borel: those on `F`, `GL_(n+1)`, the upper
   unipotent groups, `GL_1`, and the two quotients (the latter two via
   `IsJacquetNormalization.borel` and `borel_rankOne`). Substituting them turns
   `IsPairGammaFactor` into `IsGeneralPairGammaFactor` by definition.
3. The multiplicativity statement, applied with `r = n + 1` and `z = x`, gives `G i` with
   `G i` the gamma factor of `π × χ_(x i)`, and `∏ i, G i` that of `π × I(x)`. Both test
   ranks are at most `n + 1`, so the larger-rank-first relation is the ordered pair relation
   (`isGeneralSymmetricGammaFactor_of_le`).
4. `isGeneralPairGammaFactor_unramifiedTest` gives the gamma factor `G(x_i X)` of `π × χ_(x i)`. Uniqueness
   (`IsGeneralPairGammaFactor.unique`, using `q > 1`) gives `G i = G(x_i X)`. Hence
   `∏ i, G(x_i X)` is the gamma factor of `π × I(x)`.

The unitarity hypothesis on `x` in `PrincipalSeriesGammaInput` is not used.
