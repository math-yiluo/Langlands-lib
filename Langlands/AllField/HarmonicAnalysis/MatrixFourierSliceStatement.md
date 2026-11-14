# All-field port of `Langlands.HarmonicAnalysis.MatrixFourierSliceStatement`

`Langlands.AllField.HarmonicAnalysis.MatrixFourierSliceStatement` is the all-field port of the Library module `Langlands.HarmonicAnalysis.MatrixFourierSliceStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.HarmonicAnalysis.MatrixFourierSliceStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Rectangular Fourier slices of last-row cutoffs**

Statement of the scalar Fourier step in the proof of JPSS Proposition 9.1,
printed 452–454: every Schwartz–Bruhat cutoff of the last row of `g` is the
twisted rectangular integral of `x ↦ Ψ(g⁻¹ x)` for one Schwartz–Bruhat `Ψ`.
The statement is conditional on row Fourier surjectivity in the row dimension.
This is a proposition definition, not a proof.

## Imports from the port

- `Langlands.AllField.Group.GL.PadicSupplement`
- `Langlands.AllField.HarmonicAnalysis.PadicRowFourierSurjectivityStatement`

## Declarations

- `Langlands.AllField.HarmonicAnalysis.PadicMatrixFourierSliceStatement` (def): Conditional on Fourier surjectivity for rows of length `b + 1`, every
  Schwartz–Bruhat cutoff `Φ` admits a Schwartz–Bruhat function `Ψ` on
  `(b + 1) × (a + 1)` matrices with
  `∫ ψ(-x_{b,0}) Ψ(g⁻¹ x) dx = |det g|^(a + 1) Φ(lastRow g)` for every
  `g ∈ GL_{b+1}`. The integral uses the product of the supplied scalar Haar
  measure over all entries; `T` supplies the topology and the normalized
  absolute value, and the scalar measurable space is Borel.
