# All-field port of `Langlands.Representation.RankinSelberg.EqualRankAnalyticProof`

`Langlands.AllField.Representation.RankinSelberg.EqualRankAnalyticProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.EqualRankAnalyticProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.EqualRankAnalyticProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Equal-rank JPSS convergence, rationality and normalized generator**

Combine the full Whittaker expansion, finite-function Mellin analysis and quotient
Iwasawa integration with an actual unit-value test and Laurent normalization.

## Imports from the port

- `Langlands.AllField.LocalField.SmoothCharacterNormProofSupplement`
- `Langlands.AllField.Representation.CuspidalSupport.JacquetInductionStatement`
- `Langlands.AllField.Representation.Geometric.GeometricLemmaStatement`
- `Langlands.AllField.Representation.Parabolic.NormalizedJacquetStatementSupplement`
- `Langlands.AllField.Representation.RankinSelberg.DeterminantSlicesSupplement`
- `Langlands.AllField.Representation.RankinSelberg.EqualRankUnitValueProof`
- `Langlands.AllField.Representation.RankinSelberg.FiniteFunctionMellinProof`
- `Langlands.AllField.Representation.RankinSelberg.ModelAsymptoticProof`
- `Langlands.AllField.Representation.RankinSelberg.QuotientAnalyticProof`
- `Langlands.AllField.Representation.RankinSelberg.QuotientIwasawaIntegrationProof`
- `Langlands.AllField.Representation.Unramified.SphericalConstituentExistenceProof`
- `Langlands.AllField.Representation.Whittaker.TypeAsymptoticProof`

## Declarations

- `Langlands.AllField.RankinSelberg.equalRankAnalytic` (theorem): Equal-rank convergence, rational continuation, a common Laurent denominator
  and a normalized reciprocal-polynomial generator for actual JPSS integrals.
