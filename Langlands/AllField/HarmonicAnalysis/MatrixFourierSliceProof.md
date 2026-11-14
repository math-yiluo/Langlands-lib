# All-field port of `Langlands.HarmonicAnalysis.MatrixFourierSliceProof`

`Langlands.AllField.HarmonicAnalysis.MatrixFourierSliceProof` is the all-field port of the Library module `Langlands.HarmonicAnalysis.MatrixFourierSliceProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). The original module does not name `PadicField` itself; the p-adic field enters through the statements that it proves or uses. In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.HarmonicAnalysis.MatrixFourierSliceProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of the rectangular Fourier slice**

For a p-adic field, every last-row cutoff `Φ` is realized by a rectangular
Schwartz–Bruhat function `Ψ` through the twisted integral
`∫ ψ(-x_{B,1}) Ψ(g⁻¹ x) dx = |det g|^A Φ(lastRow g)`, conditional on row
Fourier surjectivity in dimension `B`. The function `Ψ` is a product over
columns: a row Fourier kernel in the first column and the characteristic
function of integral rows in the others.

## Imports from the port

- `Langlands.AllField.Group.GL.NormalizedCharacterSupplement`
- `Langlands.AllField.HarmonicAnalysis.MatrixFourierSliceStatement`
- `Langlands.AllField.HarmonicAnalysis.PadicRectangularHaarScalingProof`

## Declarations

- `Langlands.AllField.HarmonicAnalysis.padicMatrixFourierSlice` (theorem): The rectangular Fourier slice, conditional on row Fourier surjectivity in
  the row dimension.

Public declarations of the original that are not re-declared here: `Langlands.HarmonicAnalysis.matrixColumns`, `Langlands.HarmonicAnalysis.matrixColumns_apply`, `Langlands.HarmonicAnalysis.columnProduct`, `Langlands.HarmonicAnalysis.columnProduct_apply`, `Langlands.HarmonicAnalysis.exists_columnProduct_integral`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
