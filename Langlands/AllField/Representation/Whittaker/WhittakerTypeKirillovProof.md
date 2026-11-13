# All-field port of `Langlands.Representation.Whittaker.WhittakerTypeKirillovProof`

`Langlands.AllField.Representation.Whittaker.WhittakerTypeKirillovProof` is the all-field port of the Library module `Langlands.Representation.Whittaker.WhittakerTypeKirillovProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). The original module does not name `PadicField` itself; the p-adic field enters through the statements that it proves or uses. In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

The original uses the canonical topological data `F.canonicalTopologicalData` of the p-adic field. The port uses the supplied data `T : LocalFieldData F` throughout. Where the original quantifies over a p-adic field with its canonical data, the port quantifies over a field `F` and arbitrary data `T`.

Source: the original module `Langlands.Representation.Whittaker.WhittakerTypeKirillovProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Whittaker-type Kirillov surjectivity on the actual mirabolic group**

Deduce the exact JPSS inclusion from compact minimality for the actual smooth
mirabolic induction, using the coefficient and support adapters, for the topology
of the supplied data `T`.

## Imports from the port

- `Langlands.AllField.Representation.Whittaker.KirillovStatement`
- `Langlands.AllField.Representation.Whittaker.MirabolicMinimalityProof`

## Declarations

- `Langlands.AllField.whittakerTypeKirillov` (theorem): Every compactly supported modulo unipotent, smooth covariant function on
  actual mirabolic matrices is the restriction of a Whittaker coefficient.
