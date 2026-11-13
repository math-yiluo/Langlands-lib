# All-field port of `Langlands.Representation.Whittaker.ModelKirillovProof`

`Langlands.AllField.Representation.Whittaker.ModelKirillovProof` is the all-field port of the Library module `Langlands.Representation.Whittaker.ModelKirillovProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). The original module does not name `PadicField` itself; the p-adic field enters through the statements that it proves or uses. In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Except for the changes described under Proof route below, each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

The original uses the canonical topological data `F.canonicalTopologicalData` of the p-adic field, and transports a supplied realization to it (`topology_eq_canonical…`). The port uses the supplied data `T : LocalFieldData F` throughout. Where the original quantifies over a p-adic field with its canonical data, the port quantifies over a field `F` and arbitrary data `T`. The transport is then unnecessary and is omitted.

Source: the original module `Langlands.Representation.Whittaker.ModelKirillovProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Conditional Kirillov lifting into actual coefficient models**

## Proof route

The original theorem `modelKirillovTransfer` first rewrites the supplied topology
`T.topology` to the canonical topology `F.canonicalTopologicalData.topology`, using
`topology_eq_canonicalModule`, and then applies the hypothesis `h` at the canonical
topology. In the port, the hypothesis `h` (the ported `WhittakerTypeKirillovStatement`)
quantifies over arbitrary data `T : LocalFieldData F`, so the proof applies `h` at `F` and
`T` directly and needs no rewriting. The remaining steps are those of the original.

## Imports from the port

- `Langlands.AllField.Representation.Whittaker.ModelKirillovStatement`

## Declarations

- `Langlands.AllField.Whittaker.modelKirillovTransfer` (theorem): Deduce, from the assumed Whittaker-type Kirillov lifting for the same supplied
  data `T`, lifting into the coefficient image of every specified nonzero Whittaker
  functional.
