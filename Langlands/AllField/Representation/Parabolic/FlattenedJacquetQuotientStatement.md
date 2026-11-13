# All-field port of `Langlands.Representation.Parabolic.FlattenedJacquetQuotientStatement`

`Langlands.AllField.Representation.Parabolic.FlattenedJacquetQuotientStatement` is the all-field port of the Library module `Langlands.Representation.Parabolic.FlattenedJacquetQuotientStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Parabolic.FlattenedJacquetQuotientStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The flattened-to-iterated normalized Jacquet quotient**

The existing quotient map is required to be a surjective intertwiner for the
actual flattened standard action and the transported iterated action.

## Imports from the port

- `Langlands.AllField.Representation.CuspidalSupport.MinimalJacquetProof`
- `Langlands.AllField.Representation.Geometric.RefinementFunctors`

## Declarations

- `Langlands.AllField.Parabolic.FlattenedJacquetQuotientStatement` (def): The actual flattened Jacquet quotient map is an equivariant surjection
  onto the iterated normalized Jacquet module, pulled back along the constructed
  flattened Levi equivalence. This includes rank zero and arbitrary carriers.
