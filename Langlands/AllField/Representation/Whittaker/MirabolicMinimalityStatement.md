# All-field port of `Langlands.Representation.Whittaker.MirabolicMinimalityStatement`

`Langlands.AllField.Representation.Whittaker.MirabolicMinimalityStatement` is the all-field port of the Library module `Langlands.Representation.Whittaker.MirabolicMinimalityStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

The original uses the canonical topological data `F.canonicalTopologicalData` of the p-adic field. The port uses the supplied data `T : LocalFieldData F` throughout. Where the original quantifies over a p-adic field with its canonical data, the port quantifies over a field `F` and arbitrary data `T`.

Source: the original module `Langlands.Representation.Whittaker.MirabolicMinimalityStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Compact minimality in the actual mirabolic smooth induction**

Bernstein--Zelevinsky (1976), Proposition 5.15(c), printed pp.49--50, for the
mirabolic group over a nonarchimedean local field `F` with supplied data
`T : LocalFieldData F`. This module defines a proposition target; it does not prove it.

## Imports from the port

- `Langlands.AllField.LocalField.Foundation`

## Declarations

- `Langlands.AllField.Whittaker.MirabolicCompactMinimalityStatement` (def): Every nonzero subrepresentation of the standard smooth mirabolic induction
  contains its canonical compact-support subrepresentation. The matrix rank is
  `n + 1`, including rank one when `n = 0`.
