# All-field port of `Langlands.Representation.RankinSelberg.RootCoordinateStatement`

`Langlands.AllField.Representation.RankinSelberg.RootCoordinateStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RootCoordinateStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.RootCoordinateStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

The cumulative-product torus coordinates in the equal-rank JPSS integral.

## Imports from the port

- `Langlands.AllField.Group.GL.Padic`

## Declarations

- `Langlands.AllField.RankinSelberg.RootCoordinateChangeStatement` (def): The coordinate change from simple-root and final coordinates to diagonal
  entries is a continuous group automorphism preserving the actual product Haar
  measure. The remaining identities give its roots, determinant, last row and
  upper-Borel modulus. This is a proposition target, not an asserted theorem.
