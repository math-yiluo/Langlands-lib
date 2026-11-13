# All-field port of `Langlands.Representation.Jacquet.BlockCompressionStatement`

`Langlands.AllField.Representation.Jacquet.BlockCompressionStatement` is the all-field port of the Library module `Langlands.Representation.Jacquet.BlockCompressionStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Jacquet.BlockCompressionStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Normalized block compression and the upper Jacquet quotient**

This is a statement about the published compact average, with no new operator
data and no assertion of stabilization or canonical-lift bijectivity.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockIwahoriDefinitions`

## Declarations

- `Langlands.AllField.Jacquet.BlockCompressionStatement` (def): Normalized compression is multiplicative on the weak block chamber and
  intertwines the actual upper Jacquet quotient with its unnormalized Levi action.
  This is a derived translation of the laws motivating Casselman III.5.1–III.5.3,
  using the published weak-chamber factorization predicate.
