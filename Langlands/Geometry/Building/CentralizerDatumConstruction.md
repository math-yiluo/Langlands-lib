# Actual centralizer data from the universal valuation comparison

This internal construction provides
`Langlands.Geometry.Building.CentralizerDatum.ofValuationComparison` at arbitrary
universe `u`. For a connected reductive group over a nonarchimedean local field
and an actual maximal split torus, it constructs all seven fields of
`CentralizerDatum` from the exact universal
`Langlands.BruhatTits.Cartan.CentralizerValuationComparisonStatement`.

The published theorem `fieldCentralizerRepresentability` supplies a closed
group scheme representing the whole-torus centralizer on every test scheme.
The published `torusCentralizerFactor` factors the given torus through that
representative, with composite given by `torusCentralizerFactor_comp`.
The supplied universal comparison then proves bijectivity of restriction of
rational characters followed by real evaluation for this actual factor.
Classical choice selects the resulting data.

This is a data constructor derived from those existing Library declarations.
It has no independent literature assertion or source citation. It proves neither
the universal valuation comparison nor the final normalizer affine Weyl
statement. The comparison is an explicit argument; representability and the
torus factorization are supplied by existing proved results.
