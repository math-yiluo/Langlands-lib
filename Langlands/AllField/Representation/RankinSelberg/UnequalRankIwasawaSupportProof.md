# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankIwasawaSupportProof`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankIwasawaSupportProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankIwasawaSupportProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Except for the changes described under Proof route below, each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

The original uses the canonical normed-field structure `F.canonicalNormedField` of the p-adic field, and transports a supplied realization to it (`topology_eq_canonical…`). The port uses the supplied data `T : LocalFieldData F` throughout. Where the original quantifies over a p-adic field with its canonical data, the port quantifies over a field `F` and arbitrary data `T`. The transport is then unnecessary and is omitted.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankIwasawaSupportProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Proof route

One proof differs from the original: the private lemma `exists_compact_abs_bound` (every set
of elements of normalized absolute value at most `B` lies in a compact set) is re-proved
without the canonical norm of the p-adic field. Choose `m` with `B < q^m` (`q` the residue
cardinality); then `|ϖ^m z| ≤ q^{-m} B ≤ 1` for the uniformizer `ϖ`, so `z` lies in the image
of the compact ring of integers `T.Integers` under multiplication by `ϖ^{-m}`, which is
compact. This uses `normalizedAbs_prod` of this module and `normalizedAbs_uniformizer`,
`normalizedAbs_le_one_iff_mem_integers` and `isCompact_integers` from
`Langlands.LocalFieldData`.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.UnequalRankIwasawaSupportStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.normalizedAbs_prod` (theorem).
- `Langlands.AllField.RankinSelberg.diagonal_abs_last` (theorem).
- `Langlands.AllField.RankinSelberg.diagonal_abs_bound` (theorem).
- `Langlands.AllField.RankinSelberg.unequalRankIwasawaSupport` (theorem): Bounded adjacent Iwasawa ratios force a uniform compact rectangular support.
