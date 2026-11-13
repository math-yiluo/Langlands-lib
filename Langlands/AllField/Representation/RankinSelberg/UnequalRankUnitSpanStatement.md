# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankUnitSpanStatement`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankUnitSpanStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankUnitSpanStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankUnitSpanStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Unit membership in every actual unequal-rank JPSS zeta span**

This is the proposition target for the unit-span step in the proof of
JPSS Theorem 2.7, printed page 394. It does not prove that step.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AnalyticStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.UnequalRankUnitSpanStatement` (def): The Laurent span of the actual unequal-rank rational continuations contains
  one, for every allowed block and every supplied compatible measure. The hypotheses
  are exactly those of `UnequalRankAnalyticStatement`; no analytic conclusion or
  Kirillov restriction result is assumed.
