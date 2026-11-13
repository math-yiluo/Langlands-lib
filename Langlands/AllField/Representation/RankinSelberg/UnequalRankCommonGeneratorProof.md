# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankCommonGeneratorProof`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankCommonGeneratorProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankCommonGeneratorProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankCommonGeneratorProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

A normalized reciprocal polynomial common to every unequal-rank JPSS block.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.UnequalRankAnalyticProof`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankBlockSpanProof`

## Declarations

- `Langlands.AllField.RankinSelberg.unequalRankCommonGenerator` (theorem): JPSS Theorem 2.7(ii): one normalized reciprocal polynomial generates every
  allowed block at fixed unequal ranks, for the supplied topology and measures.
