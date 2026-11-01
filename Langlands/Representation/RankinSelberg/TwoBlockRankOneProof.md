# Closed rank-one test L base

Worker 468 proves exactly
`Langlands.RankinSelberg.TwoBlockLRankOneStatement.{uF,uV,uW}` with
`Langlands.RankinSelberg.twoBlockLRankOne.{uF,uV,uW}`. The theorem has no
additional premise and preserves the existing statement unchanged.

The helper `twoBlockLRankOne_of_uniform_mellin`, in
[TwoBlockModelLDivisibility](TwoBlockModelLDivisibility.md), proves this same
statement under the uniform finite-function Mellin convergence proposition.
The published closed theorem `uniformFiniteFunctionMellinConvergence`, imported
from `UniformFiniteFunctionMellinConvergenceProof`, discharges that sole premise.
Its threshold is chosen before every full additive Schwartz–Bruhat test. This
supplies the genuinely common convergence bound used by the actual coefficient
models in `ModelMatrixAnalyticData`.

The implemented divisibility route passes through the actual induced quotient
onto the block coefficient models. Full induced Whittaker type identifies the
coefficient models, while the quotient inclusion preserves each actual matrix
rational value. Forward matrix expansion and reverse realization on the actual
upper normalized induction give the product generator. Its span contains the
normalized reciprocal generator of the induced original's coefficient model,
so the induced L polynomial divides the product of block L polynomials. Choose
`e = 0` in the required equality `X ^ e * prod i, Pi i = Q * P`. These generator
comparisons come from the published `I1 = I3 = I2` proofs and full symmetric
L-polynomial existence. The helper's paired Markdown details every interface.

The published `twoBlockLRankOne_of_trivial_test` reduction constructs the actual
rank-one scalar equivalence and the actual determinant-twist induction
equivalence. It transports the complete symmetric certificates back to the
original arbitrary rank-one test representation, preserving the supplied Haar
measure and its certificate quantifiers. Independent field, test-carrier and
block-carrier universes, reducible full Whittaker-type inputs and both positive
block ranks remain quantified exactly as in the target.

This is an internal composition of published results, in the analytic setting
of JPSS, *Rankin–Selberg Convolutions* (1983), Theorem 3.1, printed pp. 404–405,
Section 5.3, printed p. 422, and Section 7.1(3), printed pp. 438–439. The registered
source `jpss-1983-rankin-selberg` has SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The implementation works directly with upper normalized induction; it does
not invoke lower induction or infer an induction equivalence from product
commutativity. No unrestricted or finite-block multiplicativity or Section 7
descendant is used. This module currently supplies only the L theorem; the
separate closed gamma base is not claimed here.
