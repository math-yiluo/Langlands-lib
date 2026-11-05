# Algebraic prerequisites for the exact chamber-simple factorization

This module proves a reduction to the existing, unchanged
`ChamberSimpleFactorizationStatement` in arbitrary universe `u`.
It composes published Library results and introduces no new assertion
from the original literature.

`ChamberSimpleFactorizationPrerequisiteReductionStatement` says that
`RootRankOneFactorizationStatement` and the actual
`CoverImageCentralizerNormKernelStatement` for every supplied
`ParahoricBuildingData` imply the exact factorization target. It does not
assert either algebraic input. In particular, the cover-image input
uses the datum's actual centralizer-zero subgroup, cover and
centralizer inclusion.

The theorem `chamberSimpleFactorizationPrerequisiteReduction` proves this
implication. First, rank-one factorization supplies the existing actual
root-ray decomposition by
`relativeRootRayDecompositionStatement_of_rootRankOneFactorizationStatement`.
Then `dynamicRootOrderedProduct_of_rayDecomposition` supplies the Dynamic
ordered-product statement. Thus Dynamic multiplication is not a third
independent premise of this reduction.

For each local field, group scheme and parahoric datum, the proof
specializes rank-one factorization to its connected reductive group and
maximal split torus. It applies the published
`simpleFactorization_of_rankOneFactorization` to the given apartment
axioms, chamber-simple affine root, its specified actual relative-root
derivative, supplied coroot and parahoric element. The result is exactly
the target's factorization, with the same equality direction and
reflected chamber. The target's chamber hypothesis is retained by
quantification; geometric simplicity already supplies it to the local
factorization theorem.

`chamberSimpleFactorizationStatement_of_minimalLeviZeroComparison`
provides a second entry point: the actual
`MinimalLeviZeroComparisonStatement` for every supplied parahoric datum
implies the needed cover-image containment by its existing intersection
comparison. Together with rank-one factorization this gives the same
exact target.

The module leaves the two algebraic proof obligations open. It is not an
unconditional proof of `ChamberSimpleFactorizationStatement`, and it
changes neither that statement nor its hypotheses. Author: Worker 1647.
