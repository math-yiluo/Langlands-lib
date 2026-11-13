# All-field port of `Langlands.Representation.Parabolic.JacquetCenterSpanStatement`

`Langlands.AllField.Representation.Parabolic.JacquetCenterSpanStatement` is the all-field port of the Library module `Langlands.Representation.Parabolic.JacquetCenterSpanStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Parabolic.JacquetCenterSpanStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Finite operator span for the unnormalized Jacquet block-scalar action**

This is a derived prerequisite for JPS (1979), Proposition (2.2) and
Remark (2.2.5), using the actual radical quotient and product-Levi action.
The proposition is stated here; its proof is a separate unit.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockIwahoriDefinitions`

## Declarations

- `Langlands.AllField.Parabolic.JacquetCenterSpanStatement` (def): The actual unnormalized Jacquet action of every block-scalar tuple has
  finite-dimensional complex operator span for admissible finite-type input.
