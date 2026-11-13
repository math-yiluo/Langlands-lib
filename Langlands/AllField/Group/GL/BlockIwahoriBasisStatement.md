# All-field port of `Langlands.Group.GL.BlockIwahoriBasisStatement`

`Langlands.AllField.Group.GL.BlockIwahoriBasisStatement` is the all-field port of the Library module `Langlands.Group.GL.BlockIwahoriBasisStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Group.GL.BlockIwahoriBasisStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockIwahoriDefinitions`
- `Langlands.AllField.Group.GL.CompactOpen`

## Declarations

- `Langlands.AllField.GeneralLinear.BlockShape.BlockIwahoriBasisStatement` (def): Every identity neighborhood in the actual local-field GL contains a compact open
  subgroup with the published weak-chamber block Iwahori factorization.
