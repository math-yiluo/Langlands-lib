# Gamma comparison on nested coefficient models

Worker 468 supplies internal support for comparing already existing JPSS gamma
certificates. The construction and proofs are derived from the published
coefficient-image definition, fixed-functional gamma equations, Fourier
uniqueness and rational-continuation uniqueness. This module makes no new
literal literature claim.

`Whittaker.coefficientModelInclusionMap` is the actual injective intertwiner
between two nested coefficient images for the same subgroup and character.
The original representations can have different carriers in independent
universes. It is the submodule inclusion and preserves the underlying
equivariant function definitionally; its equivariance follows from the
inherited right-translation actions.

`EqualRankGammaEquation.eq_of_model_le` compares two given equal-rank equations
when both smaller coefficient models are included in the respective larger
models, the smaller second functional is nonzero, and `q > 1`. Restricting the
larger model's action of minus identity to the smaller second model identifies
the two minus-one scalars by the published uniqueness theorem. Choose a
nonzero rational continuation in the smaller integral family, and apply both
functional equations to the same coefficient functions and Schwartz test.
Fourier uniqueness identifies their Fourier tests. Rational-continuation
uniqueness identifies both forward continuations with the chosen nonzero one
and identifies their dual continuations. The published
`GammaFunctionalEquation.gamma_unique` then identifies the gamma factors.

`UnequalRankGammaEquation.eq_of_model_le` makes the same comparison for
`n < r`. It uses only the block `j = 0`, `k = r - n - 1`, for which the rank
identity follows arithmetically. The actual dual integral, including its
inverse-transpose transform, block Weyl translation and exchanged rectangular
block, depends only on the unchanged coefficient functions. The two
continuation witnesses therefore have identical integral families. The same
continuation and gamma uniqueness arguments apply.

`IsEqualRankGammaFactor.eq_of_model_le` and
`IsUnequalRankGammaFactor.eq_of_model_le` lift the comparison to the existing
complete certificates. The inputs specify four nonzero functionals and the
two coefficient-model inclusions. The smaller certificate supplies a compatible
quotient measure and its right-invariance instance; both certificates' universal
clauses supply their equations for that same measure and the chosen
functionals. `IsPairGammaFactor.eq_of_model_le` then splits the rank order.
Unequal and equal ranks use the corresponding comparison; the larger-test
branch is impossible by the definition of the pair relation. The measure
existence and universal clauses of the input certificates remain intact.

The fixed-functional comparisons assume both equations; the complete-certificate
comparisons assume both certificates. Inclusion alone does not construct either equation, prove analytic
existence on a reducible carrier, or transport normalized ideal generators.
No irreducibility, full Whittaker type, topology on the original carriers,
induced representation equivalence or analytic multiplicativity is used.
Neither closed two-block rank-one analytic target is proved by this support.
