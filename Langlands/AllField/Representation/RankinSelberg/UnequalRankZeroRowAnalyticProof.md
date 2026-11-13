# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankZeroRowAnalyticProof`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankZeroRowAnalyticProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankZeroRowAnalyticProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankZeroRowAnalyticProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Zero-row unequal-rank convergence, rationality and a uniform denominator**

Assemble full-torus expansions, normalized compact averages and finite-function
Mellin analysis, then transport through quotient Iwasawa integration and the
zero-row Dirac measure.
The two Dirac reductions are reused from Worker 329's shared revision-3 draft.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.FiniteFunctionMellinProof`
- `Langlands.AllField.Representation.RankinSelberg.ModelAsymptoticProof`
- `Langlands.AllField.Representation.RankinSelberg.QuotientIwasawaIntegrationProof`
- `Langlands.AllField.Representation.RankinSelberg.QuotientRootIntegrationProof`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankZeroRowAnalyticStatement`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankZeroRowNormalizedCompactIntegrationProof`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankZeroRowRootExpansionProof`
- `Langlands.AllField.Representation.Whittaker.TypeAsymptoticProof`

## Declarations

- `Langlands.AllField.RankinSelberg.unequalRankZeroRowAnalytic` (theorem): Zero-row unequal-rank absolute convergence, rational continuation and one
  Laurent denominator for all coefficient pairs, for every positive rank gap.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.UnequalRankZeroRowAssembly.zero_row_converges_iff`, `Langlands.RankinSelberg.UnequalRankZeroRowAssembly.zero_row_integral_eq`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
