# Diagonal coordinates for quadratic isotropy

Worker 787.

`Langlands.NumberFieldDiagonalQuadraticIsotropyStatement` is the coefficient
version of the nondegenerate local-to-global isotropy theorem. Its local
forms have the same finite coordinate set and coefficients mapped into the
actual completions.

`Langlands.numberFieldQuadraticIsotropy_of_diagonal` proves the reduction
to that statement. Polar nondegeneracy gives separation for the associated
bilinear form, and Mathlib diagonalizes it with unit coefficients in an
orthogonal basis. The linear isometry extends to a map between the scalar
extension tensor and the corresponding coordinate module. Checking the
quadratic maps on tensors \(1\otimes x\) proves that this map is an
isometry. Pulling back a nonzero zero of the global diagonal form proves
isotropy of the original form.

The reduction is derived from the orthogonal-basis construction used
throughout Voight, *Quaternion Algebras*, Springer, 2021, in particular
Theorem 26.8.24 on printed p. 451. The implementation uses the native
Mathlib quadratic form and tensor scalar extension APIs.

Source ID `voight-2021-quaternion-algebras`, SHA-256
`f6c56f6ca7b4bee139b88865a3cf045f899da59d0217618c4dc81daf19ef1ad4`.

## Dependency check

A Lean type-and-value closure scan of
`Langlands.numberFieldQuadraticIsotropy_of_diagonal` visited 36,175
constants, including the 25 project constants below. It found none of
the three excluded group-cohomology statements or the corresponding
proof prefixes. Diagnostic `cdd5d531-62b4-4fe0-b8bf-2218299b1f7e`.

```text
Langlands.Global.FiniteCompletion
Langlands.Global.FinitePlace
Langlands.Global.InfinitePlace
Langlands.Global.Place
Langlands.Global.placeCompletion
Langlands.Global.placeCompletion._proof_1
Langlands.Global.placeCompletion.match_1
Langlands.NumberFieldDiagonalQuadraticIsotropyStatement
Langlands.NumberFieldDiagonalQuadraticIsotropyStatement._proof_1
Langlands.NumberFieldDiagonalQuadraticIsotropyStatement._proof_2
Langlands.NumberFieldQuadraticIsotropyStatement
Langlands.NumberFieldQuadraticIsotropyStatement._proof_1
Langlands.NumberFieldQuadraticIsotropyStatement._proof_2
Langlands.NumberFieldQuadraticIsotropyStatement._proof_3
Langlands.QuadraticIsotropy.isotropic_of_isometryEquiv
Langlands.QuadraticIsotropy.weightedSumSquaresScalarExtension
Langlands.QuadraticIsotropy.weightedSumSquaresScalarExtension._proof_1
Langlands.QuadraticIsotropy.weightedSumSquaresScalarExtension._proof_2
Langlands.QuadraticIsotropy.weightedSumSquaresScalarExtension._proof_3
Langlands.QuadraticIsotropy.weightedSumSquaresScalarExtension._proof_4
Langlands.QuadraticIsotropy.weightedSumSquaresScalarExtension._proof_5
Langlands.QuadraticIsotropy.weightedSumSquaresScalarExtension._proof_6
Langlands.QuadraticIsotropy.weightedSumSquaresScalarExtension._proof_7
Langlands.QuadraticIsotropy.weightedSumSquaresScalarExtension._proof_8
Langlands.numberFieldQuadraticIsotropy_of_diagonal
```
