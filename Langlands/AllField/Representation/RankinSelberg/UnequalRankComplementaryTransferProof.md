# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankComplementaryTransferProof`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankComplementaryTransferProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankComplementaryTransferProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankComplementaryTransferProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Paired complementary-block transfer using one original-model coefficient.
Published support, coefficient integration, Fourier smearing, conjugation and
normalized cutoff results give both inner rectangular identities. These lift
to the actual iterated quotient integrals without a quotient-variable
interchange. Both real half-plane bounds can be chosen as zero.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.PadicRowFourierCutoffProof`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankCompactSupportProof`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankComplementaryTransferStatement`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankFiniteExpansionProof`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankFourierSmearingProof`

## Declarations

- `Langlands.AllField.RankinSelberg.ComplementaryTransfer.exists_uniform_support_integrable` (theorem): The published uniform support theorem and the published coefficient
  integration theorem discharge full rectangular integrability for the actual
  supplied scalar Haar measure, before any quotient integral is considered.
- `Langlands.AllField.RankinSelberg.ComplementaryTransfer.exists_lower_average_and_dual_cutoff` (theorem): Construct a single original-model witness using the published global and
  pointwise Fourier-smearing theorem. The final assembly supplies the actual
  matrix-conjugation premise.
- `Langlands.AllField.RankinSelberg.ComplementaryTransfer.exists_lower_average_and_dual_cutoffAt` (theorem): The single-witness construction at an arbitrary equal large rank.
- `Langlands.AllField.RankinSelberg.ComplementaryTransfer.complementaryTransfer_of_row_cutoff` (theorem): Assemble the paired transfer from a normalized row cutoff proposition.
  The final theorem supplies this proposition by its published proof.
- `Langlands.AllField.RankinSelberg.unequalRankComplementaryTransfer` (theorem): One coefficient in the original model transfers both actual original and
  complementary dual integrals, with the supplied measures and independent
  field and representation universes.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.ComplementaryTransfer.fourierPair_inverse_of_even`, `Langlands.RankinSelberg.ComplementaryTransfer.exists_open_coefficient_invariance`, `Langlands.RankinSelberg.ComplementaryTransfer.reflected_plateau_integral`, `Langlands.RankinSelberg.ComplementaryTransfer.normalized_cutoff_integral`, `Langlands.RankinSelberg.ComplementaryTransfer.lower_average_integral_transfer`, `Langlands.RankinSelberg.ComplementaryTransfer.dual_cutoff_integral_transfer`, `Langlands.RankinSelberg.ComplementaryTransfer.original_rectangular_transfer`, `Langlands.RankinSelberg.ComplementaryTransfer.cutoff_rectangular_transfer`, `Langlands.RankinSelberg.ComplementaryTransfer.original_rectangular_transferAt`, `Langlands.RankinSelberg.ComplementaryTransfer.cutoff_rectangular_transferAt`, `Langlands.RankinSelberg.ComplementaryTransfer.complementary_conjugationAt`, `Langlands.RankinSelberg.ComplementaryTransfer.unequalRankIntegralAt_congr_inner`, `Langlands.RankinSelberg.ComplementaryTransfer.dual_average_pullback`, `Langlands.RankinSelberg.ComplementaryTransfer.exists_original_of_dual_average`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
