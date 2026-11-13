# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankAnalyticProof`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankAnalyticProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankAnalyticProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankAnalyticProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**JPSS unequal-rank convergence, rationality and normalized generators**

Transfer the published zero-row analytics through the published compact
rectangular expansion, retaining the actual coefficient models and measures.
The published unit-span and algebraic normalization theorems supply the
normalized generator for each block.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.UnequalRankCompactSupportProof`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankFiniteExpansionProof`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankUnitSpanProof`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankZeroRowAnalyticProof`

## Declarations

- `Langlands.AllField.RankinSelberg.UnequalRankReduction.padic_rectangular_schwartz_integrable` (theorem): The same integrability statement for the topology and Borel structure of the
  supplied data `T`.
- `Langlands.AllField.RankinSelberg.UnequalRankReduction.unequalRankAnalytic_of_prerequisites` (theorem): Assembly of all four clauses from the two remaining analytic and
  representation-theoretic prerequisites. Compact support, finite expansion and
  algebraic normalization are imported proofs, not additional premises.
- `Langlands.AllField.RankinSelberg.UnequalRankReduction.unequalRankAnalytic_of_zero_row` (theorem): The published unit-span theorem leaves only zero-row analytics as an input
  to the complete unequal-rank analytic conclusion.
- `Langlands.AllField.RankinSelberg.unequalRankAnalytic` (theorem): JPSS Theorem 2.7(i)-(ii) for every unequal-rank block, with the supplied
  topology and measures and independent representation universes.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.UnequalRankReduction.integrable_separated_sum`, `Langlands.RankinSelberg.UnequalRankReduction.integral_separated_sum`, `Langlands.RankinSelberg.UnequalRankReduction.finite_common_bound`, `Langlands.RankinSelberg.UnequalRankReduction.unequalRankMatrix_at_zero`, `Langlands.RankinSelberg.UnequalRankReduction.integrand_of_finite_expansion`, `Langlands.RankinSelberg.UnequalRankReduction.converges_of_finite_expansion`, `Langlands.RankinSelberg.UnequalRankReduction.integral_of_finite_expansion`, `Langlands.RankinSelberg.UnequalRankReduction.diagonal_integrand_eq_zero_rows`, `Langlands.RankinSelberg.UnequalRankReduction.converges_on_right_of_finite_expansion`, `Langlands.RankinSelberg.UnequalRankReduction.continuation_of_finite_expansion`, `Langlands.RankinSelberg.UnequalRankReduction.continuation_mem_span_of_finite_expansion`, `Langlands.RankinSelberg.UnequalRankReduction.analytic_of_finite_expansion`, `Langlands.RankinSelberg.UnequalRankReduction.diagonal_analytic_of_zero_row`, `Langlands.RankinSelberg.UnequalRankReduction.rectangular_schwartz_integrable`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
