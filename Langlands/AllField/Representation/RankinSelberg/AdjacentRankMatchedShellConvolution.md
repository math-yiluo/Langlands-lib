# All-field port of `Langlands.Representation.RankinSelberg.AdjacentRankMatchedShellConvolution`

`Langlands.AllField.Representation.RankinSelberg.AdjacentRankMatchedShellConvolution` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.AdjacentRankMatchedShellConvolution`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.AdjacentRankMatchedShellConvolution` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Matched actual shell convolutions with a supplied finite inner expansion.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankMatchedInnerSlices`
- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankShellConvolution`

## Declarations

- `Langlands.AllField.RankinSelberg.Padic.AdjacentRankShellConvolutionAt` (def): The actual finite shell convolution, including integrability of both
  product kernels and all quotient and group slice factors.
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankShell_finiteConvolution_of_innerSeparation` (theorem): Carry a supplied inner expansion through the actual quotient shear and
  finite determinant partition, retaining its exact family and coefficients.
- `Langlands.AllField.RankinSelberg.Padic.inverseCoefficientAsScaledStandard` (def): Recast the actual image of a specified inverse-character functional as
  the image of its scaled-standard transport, retaining the same function.
- `Langlands.AllField.RankinSelberg.Padic.AdjacentRankShellLowerBounds` (def): The actual pointwise lower support bounds used for a finite convolution.
- `Langlands.AllField.RankinSelberg.Padic.adjacentRankShell_matchedFiniteConvolution` (theorem): Original and transformed outer convolutions use one actual finite model
  family and exactly the same matrix coefficients, transformed by iota.
