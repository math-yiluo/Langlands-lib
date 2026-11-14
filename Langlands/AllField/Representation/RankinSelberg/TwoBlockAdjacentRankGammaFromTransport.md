# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockAdjacentRankGammaFromTransport`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockAdjacentRankGammaFromTransport` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockAdjacentRankGammaFromTransport`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). The original module does not name `PadicField` itself; the p-adic field enters through the statements that it proves or uses. In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

The original uses the canonical topological data `F.canonicalTopologicalData` of the p-adic field. The port uses the supplied data `T : LocalFieldData F` throughout. Where the original quantifies over a p-adic field with its canonical data, the port quantifies over a field `F` and arbitrary data `T`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockAdjacentRankGammaFromTransport` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankLowerCharacterGamma`

## Declarations

- `Langlands.AllField.RankinSelberg.AdjacentRankGammaFromTransportStatement` (def): The exact adjacent-rank gamma target follows from complete unramified gamma
  transport, retaining the latter as an explicit undischarged premise.
- `Langlands.AllField.RankinSelberg.twoBlockGammaAdjacentRank_of_transport` (theorem): The lower analytic product transports through the actual reversal of the
  ordered dependent block family.
