# All-field port of `Langlands.Representation.Whittaker.JPSBoundedDilationRecurrenceStatement`

`Langlands.AllField.Representation.Whittaker.JPSBoundedDilationRecurrenceStatement` is the all-field port of the Library module `Langlands.Representation.Whittaker.JPSBoundedDilationRecurrenceStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.JPSBoundedDilationRecurrenceStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Uniform-region recurrence for powers of a bounded coordinate dilation**

For an actual JPS function space with a finite coordinate operator span, the
powers of one bounded coordinate dilation satisfy one scalar linear recurrence
pointwise on a whole small-coordinate region. This module defines a proposition
only.

## Imports from the port

- `Langlands.AllField.Representation.Whittaker.JPSFunctionSpace`

## Declarations

- `Langlands.AllField.Whittaker.JPSBoundedDilationRecurrenceStatement` (def): Derived from the proof of JPS (1979), Lemma (2.2.1): if the actual coordinate
  germ action `σ_i` has a finite-dimensional operator span, then for every unit `c`
  with `|c| ≤ 1` there are one length `D` and one family of scalar coefficients
  `d m j`, both chosen before every function, such that for each `f` one positive
  threshold, chosen before every power `m` and the whole torus tuple, makes every
  `ρ_i(c ^ m) f` equal to `∑ j < D, d m j • ρ_i(c ^ j) f` pointwise below it.
