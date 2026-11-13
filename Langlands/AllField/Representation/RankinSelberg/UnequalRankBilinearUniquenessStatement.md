# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Unequal-rank bilinear uniqueness for Whittaker-type coefficient models**

The covariance is JPSS (2.11.2) and (2.11.4). The full Whittaker-type
uniqueness target is an internal extension needed for the scope of Theorem
2.7; the printed Proposition on p.399 assumes irreducible generic data.
This module states the extension and does not prove it.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AnalyticStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.UnequalRankBilinearUniquenessStatement` (def): Full Whittaker-type unequal-rank bilinear uniqueness outside a finite
  set of spectral values. This internal extension of the irreducible generic
  Proposition in JPSS Section 2.11 remains a proof obligation.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.IsUnequalRankCovarianceUnipotent`, `Langlands.RankinSelberg.IsUnequalRankBilinearCovariant`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
