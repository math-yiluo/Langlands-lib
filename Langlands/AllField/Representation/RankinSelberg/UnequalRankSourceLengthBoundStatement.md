# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankSourceLengthBoundStatement`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankSourceLengthBoundStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankSourceLengthBoundStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankSourceLengthBoundStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Uniform source-carrier length bound for unequal-rank Whittaker-type data**

An internal intermediate target for the full Whittaker-type
`UnequalRankBilinearUniquenessStatement`: outside finitely many spectral
values, the published space `unequalRankMirabolicForms` on the original
carriers has length at most one. The first representation is restricted to
its mirabolic subgroup; the second stays on `GL_(n+1)`. This is not the
irreducible Lemma or Proposition of JPSS p.399, and it is not proved here.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.UnequalRankSourceLengthBoundStatement` (def): For Whittaker-type data, there is a finite set of spectral values
  `q^(-s)` outside which the actual unequal-rank covariant forms on the
  original carriers, with only the first representation restricted to its
  mirabolic subgroup, form a complex module of length at most one.
