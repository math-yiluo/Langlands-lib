# All-field port of `Langlands.Representation.Geometric.BruhatMatrixStatement`

`Langlands.AllField.Representation.Geometric.BruhatMatrixStatement` is the all-field port of the Library module `Langlands.Representation.Geometric.BruhatMatrixStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.Representation.Geometric.BruhatMatrixStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Matrix existence and Weyl-class reflection prerequisites for local-field Bruhat.

## Imports from the port

- `Langlands.AllField.Group.GL.Padic`

## Declarations

- `Langlands.AllField.Geometric.PadicBruhatMatrixExistenceTheorem` (def): Every parabolic double coset contains the inverse matrix of an actual
  permutation, without requiring that permutation to be minimal.
- `Langlands.AllField.Geometric.PadicBruhatWeylReflectionTheorem` (def): Equality of inverse permutation-matrix classes reflects equality of the
  corresponding Weyl double cosets, with the block subgroups in reversed order.
