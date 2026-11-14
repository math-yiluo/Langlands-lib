# All-field port of `Langlands.Representation.RankinSelberg.LowerBlockWeightedProductInvariance`

`Langlands.AllField.Representation.RankinSelberg.LowerBlockWeightedProductInvariance` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.LowerBlockWeightedProductInvariance`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.LowerBlockWeightedProductInvariance` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Invariance of the determinant-weighted lower-block product**

The exact determinant density on the small lower triangular group cancels
the determinant scaling of its right action on the rectangular coordinate.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.PadicRectangularHaarScalingProof`
- `Langlands.AllField.Representation.RankinSelberg.LowerBlockQuotientMeasureSupport`

## Declarations

- `Langlands.AllField.RankinSelberg.lowerTriangularBlockDensity` (def): The representative density `|det b|^(-d)` on the actual small lower
  triangular group. It is the pullback of the published quotient density.
- `Langlands.AllField.RankinSelberg.lowerTriangularBlockDensity_eq_coe` (theorem).
- `Langlands.AllField.RankinSelberg.continuous_lowerTriangularBlockDensity` (theorem).
- `Langlands.AllField.RankinSelberg.map_lowerTriangularBlockDensity_mulRight` (theorem): Right translation of the weighted triangular factor has exactly the
  positive determinant multiplier that cancels rectangular right scaling.
- `Langlands.AllField.RankinSelberg.map_rectangularMeasure_mulRight` (theorem): The rectangular additive factor scales by the inverse determinant
  multiplier under right multiplication by the small block.
- `Langlands.AllField.RankinSelberg.measurePreserving_lowerBlockWeightedProduct_diagonal` (theorem): Simultaneous right translation of the two triangular factors and right
  linear change of the rectangular coordinate preserves the weighted product.
- `Langlands.AllField.RankinSelberg.measurePreserving_lowerBlockWeightedProduct_shear` (theorem): A triangular-dependent additive translation of the rectangular factor
  preserves the weighted product.
- `Langlands.AllField.RankinSelberg.measurePreserving_lowerBlockWeightedProduct_mulRight` (theorem): The actual lower-block right multiplication in parameter coordinates
  preserves the determinant-weighted right-associated product measure.
