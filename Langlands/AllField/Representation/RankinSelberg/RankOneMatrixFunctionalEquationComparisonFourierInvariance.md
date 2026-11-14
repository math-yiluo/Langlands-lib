# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierInvariance`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierInvariance` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierInvariance`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierInvariance` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Compact and finite-order symmetries in actual matrix Fourier tests**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport`

## Declarations

- `Langlands.LocalFieldData.determinantNorm_eq_one_of_pow_eq_one` (theorem): A finite-order matrix has determinant norm one.
- `Langlands.LocalFieldData.determinantNorm_permutation` (theorem): Every actual permutation matrix has determinant norm one.
- `Langlands.LocalFieldData.determinantNorm_weylLong` (theorem): The unsigned long Weyl representative has determinant norm one.
- `Langlands.AllField.GodementJacquet.padicMatrixFourierPair_leftRight_invariant` (theorem): A left-right symmetry of a test transfers to the corresponding
  inverse-transpose symmetry of its actual full Fourier partner.
- `Langlands.AllField.GodementJacquet.padicMatrixFourierPair_compact_left_invariant` (theorem): Left invariance under a compact subgroup becomes left invariance of the
  Fourier partner under its actual inverse-transpose image.

Public declarations of the original that are not re-declared here: `Langlands.HarmonicAnalysis.rectangularLeftInvariantTests`, `Langlands.HarmonicAnalysis.mem_rectangularLeftInvariantTests`, `Langlands.PadicField.TopologicalData.determinantNorm_signDiagonal`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
