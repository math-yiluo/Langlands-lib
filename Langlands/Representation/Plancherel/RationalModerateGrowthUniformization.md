# The finite-length step on actual reductive rational points

Author: Worker 1564.

`Langlands.Plancherel.rationalFiniteLengthModerateGrowth_of_coefficientGrowth`
derives `RationalFiniteLengthModerateGrowthStatement.{u,uV}` from
`RationalCoefficientModerateGrowthStatement.{u,uV}`. It uses the actual
residue-normalized matrix norm, canonical rational-point topology, and
independent field and representation-carrier universes of those statements.
All supplied closed matrix embeddings remain quantified.

The auxiliary `rationalPoint_compactOpenCofinal` proves compact-open cofinality
for every affine group scheme locally of finite type over the supplied
nonarchimedean local field. The published
`BruhatTits.rationalPoint_isLocallyProfinite` gives local profiniteness of its
actual identity-test rational points in their canonical topology. The published
`Topology.LocallyProfiniteProof.vanDantzig` then provides a compact open
subgroup inside each supplied open subgroup, using that subgroup as an identity
neighborhood. This helper does not assume reductivity, a matrix embedding, or a
separately supplied nonarchimedean group structure.

For the moderate-growth implication, connected reductivity supplies affineness
and smoothness, hence the local finite-type condition. The cofinality helper
applies to this same point group and topology. The proved lower bound
`one_le_rationalMatrixNorm` and multiplication estimate
`rationalMatrixNorm_mul_le` discharge the two height conditions of
`finiteLengthCoefficientGrowthUniformization`. Specializing the coefficientwise
premise to the given field, group, embedding and representation supplies its
last premise. The result is exactly the uniform-exponent conclusion, with a
positive real constant still allowed to depend on the coefficient pair.

This is an internal application of the algebraic uniformization proof and the
published local-profinite point topology results. It formalizes the
finite-length step of the I.4.4 prerequisite; it does not establish its
coefficientwise premise. The full intertwining theorem still requires that
growth estimate and its analytic and rational-continuation conclusions.
