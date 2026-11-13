# All-field port of `Langlands.Representation.Parabolic.NormalizedJacquetAdmissibilityProof`

`Langlands.AllField.Representation.Parabolic.NormalizedJacquetAdmissibilityProof` is the all-field port of the Library module `Langlands.Representation.Parabolic.NormalizedJacquetAdmissibilityProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Parabolic.NormalizedJacquetAdmissibilityProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockIwahoriBasis`
- `Langlands.AllField.Representation.Jacquet.CanonicalLiftBijectivityProof`
- `Langlands.AllField.Representation.Jacquet.Parabolic`
- `Langlands.AllField.Representation.Parabolic.NormalizedJacquetStatement`

## Declarations

- `Langlands.AllField.Parabolic.jacquetModuleEquiv_leviCoinvariants` (theorem): The existing quotient comparison intertwines the actual product and embedded
  Levi actions.
- `Langlands.AllField.Parabolic.isSmooth_leviCoinvariants` (theorem): Smoothness of the actual untwisted product-Levi quotient.
- `Langlands.AllField.Parabolic.exists_iwahori_levi_subset` (theorem): A small ambient Iwahori subgroup has Levi intersection inside any prescribed
  open subgroup of the product Levi.
- `Langlands.AllField.Parabolic.isAdmissible_leviCoinvariants` (theorem): Admissibility of the actual untwisted product-Levi quotient.
- `Langlands.AllField.Parabolic.normalizedJacquetAdmissibility` (theorem): The complete published clause, with independent field and carrier universes.
