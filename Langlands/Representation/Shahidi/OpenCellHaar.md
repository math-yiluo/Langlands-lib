# Integrals of lattice-periodic functions on rectangular matrix spaces

Module `Langlands.Representation.Shahidi.OpenCellHaar`, namespace
`Langlands.Shahidi.OpenCell`.

## Contents

- `haarK K`: the additive Haar measure on `K` with `vol(𝒪) = 1`; `matrixHaar K a b`: the product
  measure `RankinSelberg.rectangularMeasure` on `M_(a×b)(K)`, an additive Haar measure with
  `vol(M_(a×b)(𝒪)) = 1` (`matrixHaar_integralMatrices`).
- `IsLatticePeriodic K G`: invariance under translation by `integralMatrices K a b`;
  `continuous_of_isLatticePeriodic`: such functions are locally constant.
- `integrable_and_hasSum_of_isLatticePeriodic`: a lattice-periodic function whose values on the
  classes are absolutely summable is integrable, and its integral is the sum of its values over
  the classes of `M_(a×b)(K) / M_(a×b)(𝒪)`.

## Provenance

Standard measure theory: each class is a translate of `M_(a×b)(𝒪)`, of measure one.
