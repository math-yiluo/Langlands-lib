# Conditional compactness of the actual centralizer norm kernel

This internal derived unit connects the actual centralizer supplied by
`ParahoricBuildingData` to the central maximal split-torus quotient route. It
uses named group-scheme and rational-point interfaces. No new external source
claim is used independently.

`isCompact_rationalCommonNormKernel_of_central_maximalSplit` explicitly assumes
the whole `CentralQuotientReductiveStatement` and
`AnisotropicCompactnessStatement` at arbitrary universe `u`. For a connected
reductive group over any nonarchimedean local field and a specified central
maximal split torus, it concludes compactness of the actual rational common norm
kernel in `rationalPointTopology F G.X`. It constructs the actual smooth affine
anisotropic quotient by the full all-test range of that torus. Smoothness gives
local finite type of the quotient. Centrality puts the kernel functor inside
the scheme centre, so the explicitly assumed central-quotient reductivity
statement applies. The central split quotient compactness adapter then applies
the explicitly assumed anisotropic compactness statement. The projection is
open on rational points by its smooth represented torus kernel, as established
in that adapter. No surjectivity on rational points is inferred.

`centralizer_isCentral_maximalSplit` is unconditional for every actual supplied
`ParahoricBuildingData P`. The inclusion `P.centralizer.j` represents the whole
all-test centralizer of `P.i` and is closed. The supplied factorization
`P.centralizer.s` composes with that inclusion to `P.i`. The represented
centralizer property makes this same factor central; closedness and maximal
splitness of the ambient torus transfer maximal splitness to this factor. This
uses no connected-reductivity certificate for the centralizer and no apartment
axiom.

`ActualCentralizerNormKernelCompactnessReductionStatement` explicitly assumes
the entire `ActualCentralizerStructureStatement`,
`CentralQuotientReductiveStatement` and `AnisotropicCompactnessStatement` at the
same universe `u`. For the actual supplied `P`, its conclusion is compactness of
`rationalCommonNormKernel P.centralizer.Z` as a subset of the full actual
centralizer point group in exactly its canonical rational-point topology. The
affine structure is derived from the supplied closed centralizer inclusion, as
in the centralizer-zero target.

`actualCentralizerNormKernelCompactnessReduction` proves this conditional
proposition. It applies the retained structure statement to the actual group,
maximal split torus, closed represented centralizer, and same factorization in
`P`. The resulting reductivity witness and the unconditional centrality and
maximal splitness just proved supply the generic compactness theorem.

All three whole-statement inputs remain proof obligations. This unit does not
prove any of them and does not prove `CentralizerZeroCompactOpenStatement`.
Passing from the norm kernel to the actual centralizer-zero subgroup still
requires its containment and closedness, for example through independently
proved openness. Both local-field characteristics and split rank zero are
retained.
