# All-field port of `Langlands.Representation.CuspidalSupport.AssociatedConditional`

`Langlands.AllField.Representation.CuspidalSupport.AssociatedConditional` is the all-field port of the Library module `Langlands.Representation.CuspidalSupport.AssociatedConditional`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.CuspidalSupport.AssociatedConditional` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.Representation.CuspidalSupport.AssociatedAssembly`
- `Langlands.AllField.Representation.CuspidalSupport.AssociatedRankZero`

## Declarations

- `Langlands.AllField.CuspidalSupport.associatedJacquetFiltration_of_geometricPieces` (theorem): Assemble the actual associated Jacquet filtration and its quasicuspidality
  from the individual geometric inputs and zero-factor deletion.
- `Langlands.AllField.CuspidalSupport.associatedJacquetFiltration_of_prerequisites` (theorem): The full rank split, with the remaining geometric and deletion proof
  obligations explicit. This helper is not the unconditional theorem.
