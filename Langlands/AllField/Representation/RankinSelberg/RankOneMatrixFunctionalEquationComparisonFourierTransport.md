# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Actual left-right changes of variables in the matrix Fourier pairing**

Internal Fourier transport helpers for the matrix-to-rank-one comparison.
These results do not assert the matrix-to-Whittaker analytic passage.

## Imports from the port

- `Langlands.AllField.Group.GL.NormalizedCharacterSupplement`
- `Langlands.AllField.HarmonicAnalysis.PadicRectangularHaarScalingProof`
- `Langlands.AllField.Representation.GodementJacquet.AnalyticData`

## Declarations

- `Langlands.AllField.HarmonicAnalysis.padicRectangularLeftRight_measurePreserving` (theorem): Determinant-norm-one left-right multiplication preserves every actual
  rectangular additive Haar measure, including the empty-dimensional cases.
- `Langlands.AllField.HarmonicAnalysis.padicRectangularFourierIntegral_leftRight` (theorem): The plus transpose Fourier integral has no extra scalar under
  determinant-norm-one left-right multiplication, for every supplied scalar Haar
  measure and every character.

Public declarations of the original that are not re-declared here: `Langlands.HarmonicAnalysis.rectangularPairing_transpose`, `Langlands.HarmonicAnalysis.rectangularPairing_mul_right`, `Langlands.HarmonicAnalysis.rectangularPairing_mul_left`, `Langlands.HarmonicAnalysis.rectangularLeftRightHomeomorph`, `Langlands.HarmonicAnalysis.rectangularLeftRightHomeomorph_apply`, `Langlands.HarmonicAnalysis.rectangularLeftRightTranslate`, `Langlands.HarmonicAnalysis.rectangularLeftRightTranslate_apply`, `Langlands.HarmonicAnalysis.rectangularFourierIntegral_leftRight`, `Langlands.GodementJacquet.padicMatrixFourierPair_leftRight`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
