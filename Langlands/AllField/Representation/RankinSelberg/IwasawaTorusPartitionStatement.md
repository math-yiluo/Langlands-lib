# All-field port of `Langlands.Representation.RankinSelberg.IwasawaTorusPartitionStatement`

`Langlands.AllField.Representation.RankinSelberg.IwasawaTorusPartitionStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.IwasawaTorusPartitionStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.IwasawaTorusPartitionStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Measurable uniformizer-coset partition of the diagonal torus**

This is an internal measurable partition of the diagonal torus into the
uniformizer cosets of its integral units, with normalized product Haar mass
one on every coset. It assumes no partition, Haar decomposition or quotient
measure. This module does not prove the statement.

## Imports from the port

- `Langlands.AllField.Group.GL.Padic`

## Declarations

- `Langlands.AllField.RankinSelberg.IwasawaTorusPartitionStatement` (def): The diagonal torus is the disjoint union, over all exponent vectors, of the
  measurable cosets `t(lam) * U` of the integral units. Every coset is the
  translate of the normalized product Haar measure on `U` and has mass one.
