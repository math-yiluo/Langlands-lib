# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankBlockSpanProof`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankBlockSpanProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankBlockSpanProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankBlockSpanProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Equality of adjacent JPSS block spans using supplied-measure integration
and Fourier smearing in the original coefficient model.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.PadicRowFourierSurjectivityProof`
- `Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatement`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankBlockSpanStatement`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankCompactSupportProof`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankFiniteExpansionProof`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankFourierSmearingProof`

## Declarations

- `Langlands.AllField.RankinSelberg.AdjacentBlockReduction.adjacentBlockSpan_of_support_fourier` (theorem): The exact published adjacent-span target reduces to uniform compact support
  and Fourier preimages for the supplied Haar. The published smearing theorem
  constructs every needed same-model cutoff.
- `Langlands.AllField.RankinSelberg.AdjacentBlockReduction.adjacentBlockSpan_of_fourier` (theorem): The published compact-support theorem discharges the support premise.
  Only Fourier preimages for every supplied Haar remain as a hypothesis.
- `Langlands.AllField.RankinSelberg.unequalRankAdjacentBlockSpan` (theorem): Adjacent unequal-rank JPSS blocks have equal Laurent spans for every
  supplied topology and additive Haar measure.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.AdjacentBlockReduction.exists_lastRow_integral_coefficient`, `Langlands.RankinSelberg.AdjacentBlockReduction.exists_normalized_lastRow_cutoff`, `Langlands.RankinSelberg.AdjacentBlockReduction.exists_adjacent_block_integral_coefficient`, `Langlands.RankinSelberg.AdjacentBlockReduction.exists_reverse_adjacent_block_integral_coefficient`, `Langlands.RankinSelberg.AdjacentBlockReduction.exists_adjacent_integral_coefficient`, `Langlands.RankinSelberg.AdjacentBlockReduction.exists_reverse_adjacent_integral_coefficient`, `Langlands.RankinSelberg.AdjacentBlockReduction.adjacent_values_subset_of_support`, `Langlands.RankinSelberg.AdjacentBlockReduction.adjacent_values_eq_of_support_cutoff`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
