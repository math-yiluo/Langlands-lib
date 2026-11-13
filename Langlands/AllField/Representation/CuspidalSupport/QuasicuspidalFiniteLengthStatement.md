# All-field port of `Langlands.Representation.CuspidalSupport.QuasicuspidalFiniteLengthStatement`

`Langlands.AllField.Representation.CuspidalSupport.QuasicuspidalFiniteLengthStatement` is the all-field port of the Library module `Langlands.Representation.CuspidalSupport.QuasicuspidalFiniteLengthStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.CuspidalSupport.QuasicuspidalFiniteLengthStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Finite length of finitely generated admissible quasicuspidal Levi representations**

The cuspidal subcase of the finite-type finite-length argument of Silberger
(1979), Theorem 5.4.1.6, on actual standard product Levis, with the elementary
empty-product extension. This module defines a proposition; it does not prove it.

## Imports from the port

- `Langlands.AllField.Group.GL.Padic`

## Declarations

- `Langlands.AllField.CuspidalSupport.LeviQuasicuspidalFiniteLengthStatement` (def): Every admissible finitely generated quasicuspidal representation of an actual
  standard product Levi has finite length over its group algebra. All ranks,
  including zero, and independent field and representation universes are retained.
