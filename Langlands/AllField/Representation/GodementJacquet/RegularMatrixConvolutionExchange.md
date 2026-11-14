# All-field port of `Langlands.Representation.GodementJacquet.RegularMatrixConvolutionExchange`

`Langlands.AllField.Representation.GodementJacquet.RegularMatrixConvolutionExchange` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.RegularMatrixConvolutionExchange`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.GodementJacquet.RegularMatrixConvolutionExchange` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Actual convolution exchange for Fourier-regular matrix tests.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.SquareFourierCrossExchange`
- `Langlands.AllField.Representation.GodementJacquet.InverseTransposeMatrixIntegral`
- `Langlands.AllField.Representation.GodementJacquet.RegularMatrixHaarDensity`

## Declarations

- `Langlands.AllField.GodementJacquet.Padic.dualWeightedRegularMatrixTest` (def): The complementary weighted test pulled back by the actual inverse transpose.
- `Langlands.AllField.GodementJacquet.Padic.dualWeightedRegularMatrixTest_apply` (theorem).
- `Langlands.AllField.GodementJacquet.Padic.determinantWeight_inv_inverseTranspose` (theorem): Inverting an inverse transpose leaves the determinant unchanged.
- `Langlands.AllField.GodementJacquet.Padic.dualWeightedRegularMatrixTest_convolution_left` (theorem): The left convolution kernel after the measure-preserving inverse transpose.
- `Langlands.AllField.GodementJacquet.Padic.dualWeightedRegularMatrixTest_convolution_right` (theorem): The right convolution kernel expressed with the same determinant density.
- `Langlands.AllField.GodementJacquet.Padic.determinantWeight_neg_dimension` (theorem): The Jacobian in square Fourier exchange is the negative dimension weight.
- `Langlands.AllField.GodementJacquet.Padic.dualWeightedRegularMatrixTest_convolution_cross` (theorem): Actual Hecke convolution exchange on tests regular on both Fourier sides.
- `Langlands.AllField.GodementJacquet.Padic.regularMatrixZetaOperator_inverseTranspose` (theorem): Inverse-transpose pullback of the weighted test gives the actual zeta
  operator for the representation composed with inverse transpose.
- `Langlands.AllField.GodementJacquet.Padic.regularMatrixZetaOperator_inverseTranspose_cross` (theorem): The actual original and transformed zeta operators satisfy the cross
  identity, with composition in the order supplied by Hecke convolution.
