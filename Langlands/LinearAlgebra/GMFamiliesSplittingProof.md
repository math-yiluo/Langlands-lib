# Arthur's product splitting formula

`Langlands.GMFamily.splittingFormula` proves `Langlands.GMFamily.SplittingFormulaStatement` of [GMFamiliesStatement](GMFamiliesStatement.md). The equality is for the defining expressions on the complement of finitely many proper hyperplanes in the imaginary dual of a Levi flat. It uses the parameter projection onto the space of each face and the `dPrime` coefficients of (17.7).

## Proof

For a regular chamber `P`, expand `dPrime` in the right side of the chamber inversion (17.9). For a fixed outer face `Q'`, the intermediate faces are indexed by the subsets \(J\subseteq I\), where \(I\) is the set of chamber simple roots vanishing on `Q'`. Nested projections give the same parameter on `Q'` throughout this interval, so `famRestrict` uses one common value there. The dimension difference in the sign is \(|I|-|J|\).

The ordinary theta factor for the Levi of the intermediate face uses the roots in \(J\). The hatted factor uses the complementary Gram duals in the span of the roots in \(I\). [GMFamiliesFaceTheta](GMFamiliesFaceTheta.md) proves both identifications for the definitions in the Library. [GMFamiliesTheta](GMFamiliesTheta.md) evaluates the alternating sum by a determinant. It vanishes for every proper face of `P`, and the singleton interval with `Q' = P` contributes one. In this interval `famRestrict` evaluates `d P` at the original parameter. This proves the inversion.

Apply the inversion to each chamber term of the product sum. Reordering the finite sums and indexing the chambers incident to each face by the chambers of its Levi gives `cQM`. The exceptional set consists of the nonzero ordinary chamber simple vectors and the nonzero Gram dual vectors from the intervals used in the determinant calculation. The proof uses the root-set and Levi-space hypotheses. It in fact applies to arbitrary coefficient functions in the defining expressions, since the values at each proper outer face cancel with their common choice of chamber.

## Source

J. Arthur, *An introduction to the trace formula*, §17, printed pp. 97–98 (PDF pp. 109–110), Lemma 17.4 and equations (17.7)–(17.9), in the volume registered as `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`. SHA-256 of the retained PDF `88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`.

The proof follows the inversion and rearrangement in the source. The determinant argument supplies the alternating coefficient cancellation with the Euclidean volumes fixed in [GMFamilies](GMFamilies.md).
