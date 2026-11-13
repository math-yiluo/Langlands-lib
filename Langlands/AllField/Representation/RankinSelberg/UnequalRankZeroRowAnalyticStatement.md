# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankZeroRowAnalyticStatement`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankZeroRowAnalyticStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankZeroRowAnalyticStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankZeroRowAnalyticStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Zero-row unequal-rank convergence, rationality and a common denominator**

This proposition isolates the first three analytic conclusions at zero rows
for every positive rank gap. It is a statement target, not an analytic proof.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AnalyticStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.UnequalRankZeroRowAnalyticStatement` (def): The diagonal restriction integrals in JPSS p.394, equation (7), converge
  in a right half-plane and have rational continuations with a common denominator
  over all coefficient-model functions. The ranks differ by the arbitrary positive
  gap `k + 1`; all hypotheses are those of `UnequalRankAnalyticStatement F T n 0 k`.
  Normalized-generator existence and unit-span membership are separate targets.
