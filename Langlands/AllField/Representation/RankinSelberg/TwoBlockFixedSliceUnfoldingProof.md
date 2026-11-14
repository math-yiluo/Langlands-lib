# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockFixedSliceUnfoldingProof`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockFixedSliceUnfoldingProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockFixedSliceUnfoldingProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). The original module does not name `PadicField` itself; the p-adic field enters through the statements that it proves or uses. In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockFixedSliceUnfoldingProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The actual fixed-slice first unfolding of JPSS Section 4.6**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockFixedSliceAnalysis`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockFixedSliceUnfoldingStatement`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergenceProof`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentQuotientIntegrationProof`
- `Langlands.AllField.Representation.RankinSelberg.WhittakerRowSliceCompactSupportProof`

## Declarations

- `Langlands.AllField.RankinSelberg.twoBlockFixedSliceUnfolding` (theorem): Absolute convergence and the normalized first unfolding on every determinant slice,
  with the supplied self-dual rectangular measure and its integral-cube mass retained.
