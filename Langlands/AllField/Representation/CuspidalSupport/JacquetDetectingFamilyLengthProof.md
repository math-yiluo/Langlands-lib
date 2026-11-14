# All-field port of `Langlands.Representation.CuspidalSupport.JacquetDetectingFamilyLengthProof`

`Langlands.AllField.Representation.CuspidalSupport.JacquetDetectingFamilyLengthProof` is the all-field port of the Library module `Langlands.Representation.CuspidalSupport.JacquetDetectingFamilyLengthProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.CuspidalSupport.JacquetDetectingFamilyLengthProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.Representation.CuspidalSupport.JacquetDetectingFamilyLengthStatement`
- `Langlands.AllField.Representation.Parabolic.NormalizedJacquetExactnessProof`

## Declarations

- `Langlands.AllField.CuspidalSupport.JacquetDetectingFamilyLengthProof.jacquet_injective` (theorem): Normalized Jacquet descent preserves injections of smooth representations.
- `Langlands.AllField.CuspidalSupport.JacquetDetectingFamilyLengthProof.jacquet_length_le` (theorem): Consequently Jacquet module length is monotone under smooth injections.
- `Langlands.AllField.CuspidalSupport.JacquetDetectingFamilyLengthProof.jacquet_length_step` (theorem): Additivity on the actual Jacquet sequence of nested subspaces.
- `Langlands.AllField.CuspidalSupport.jacquetDetectingFamilyLength` (theorem): A finite family of normalized Jacquet functors detecting all nonzero
  subquotients bounds both module length and actual composition-series length.

Public declarations of the original that are not re-declared here: `Langlands.CuspidalSupport.JacquetDetectingFamilyLengthProof.lower`, `Langlands.CuspidalSupport.JacquetDetectingFamilyLengthProof.inclusion`, `Langlands.CuspidalSupport.JacquetDetectingFamilyLengthProof.inclusion_exact`, `Langlands.CuspidalSupport.JacquetDetectingFamilyLengthProof.quotient_nontrivial`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
