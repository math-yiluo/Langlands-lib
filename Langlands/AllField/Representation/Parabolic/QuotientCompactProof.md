# All-field port of `Langlands.Representation.Parabolic.QuotientCompactProof`

`Langlands.AllField.Representation.Parabolic.QuotientCompactProof` is the all-field port of the Library module `Langlands.Representation.Parabolic.QuotientCompactProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Parabolic.QuotientCompactProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.Representation.Parabolic.GeometricPrerequisitesStatement`

## Declarations

- `Langlands.AllField.Parabolic.isCompact_integralRange` (theorem): The integral group of every rank, including rank zero, is compact for the
  supplied topology.
- `Langlands.AllField.Parabolic.quotientMap_image_integralRange` (theorem): Every right coset `P * g` of the actual block parabolic meets the integral group.
- `Langlands.AllField.Parabolic.parabolicQuotientCompact` (theorem): The actual quotient `P \ G` of `GL_n(F)` by a standard block parabolic is compact,
  for the supplied topology, every block shape and every rank including zero.
