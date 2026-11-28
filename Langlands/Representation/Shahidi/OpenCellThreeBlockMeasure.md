# The change of variables between the two three-block coordinate systems

Module `Langlands.Representation.Shahidi.OpenCellThreeBlockMeasure`, namespace
`Langlands.Shahidi.OpenCell`.

## Contents

- `columnEquiv`, `rowEquiv`: splittings of `Fin (1 + (d+1))` and `Fin ((d+1) + (t+1))`.
- `columnSplitEquiv`, `rowSplitEquiv`: the measurable equivalences splitting off the last column
  of a matrix and splitting the rows of a column, with
  `measurePreserving_columnSplitEquiv`, `measurePreserving_rowSplitEquiv` for `matrixHaar`.
- `shearEquiv`: `((Y_a, z), Y_b) ↦ ((Y_a, z), Y_b - Y_a z)`, measure preserving since it is a
  translation for fixed `(Y_a, z)` (`MeasurePreserving.skew_product`).
- `threeBlockChange`: the composite measurable equivalence
  `(Y, z) ↦ (headColumns Y, shearColumn Y z)` (`threeBlockChange_apply`), and
  `measurePreserving_threeBlockChange` for the product Haar measures.

## Provenance

Standard measure theory for product Haar measures.
