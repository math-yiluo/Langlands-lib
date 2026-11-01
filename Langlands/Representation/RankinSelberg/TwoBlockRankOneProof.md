# Closed rank-one test gamma and L bases

Worker 468 proves exactly the two existing propositions
`Langlands.RankinSelberg.TwoBlockGammaRankOneStatement.{uF,uV,uW}` and
`Langlands.RankinSelberg.TwoBlockLRankOneStatement.{uF,uV,uW}` with
`twoBlockGammaRankOne` and `twoBlockLRankOne`, respectively. Both theorems
are closed compositions of published proofs. The statements retain `r = 0`,
an arbitrary full Whittaker-type rank-one test representation, both positive
block ranks, and the actual canonical normalized upper induction.

The gamma theorem applies `twoBlockGammaRankOne_of_generic_matrix`, from
[TwoBlockModelGamma](TwoBlockModelGamma.md), to the closed
`Langlands.GodementJacquet.genericMatrixFunctionalEquation.{uF,uF}` theorem,
from
[GenericMatrixFunctionalEquationProof](../GodementJacquet/GenericMatrixFunctionalEquationProof.md).
This discharges the helper's sole analytic premise. Its carrier universe is
specialized to the field universe because the actual generic socles of the
coefficient models have that universe. The original block and test carriers
still have the independent universes `uW` and `uV` of the existing target.
The generic matrix theorem itself supplies full normalized matrix data on
every actual irreducible Whittaker-type representation; its proof combines
the closed Tate and higher-rank supercuspidal analytic bases through the
published irreducible reduction.

The gamma helper chooses nonzero functionals on the original blocks and
their actual irreducible generic model socles. The generic matrix theorem
supplies both normalized polynomials, the complex unit and the integer
exponent on each socle. Admissible Schur supplies the socles' scalar central
quasicharacters, and the two-block matrix induction theorem supplies the
product data on their actual normalized upper induction. The generic socle
of the original induced coefficient model occurs as an actual subquotient
of this induction. The submodel ambient comparison therefore identifies
its rational gamma expression. Independently proved gamma existence on the
original full Whittaker-type representations supplies their complete
symmetric certificates, including when the originals are reducible.

The exact rational product identity then identifies the induced gamma
factor with the product of the two block factors. The certificate exchange
includes equal rank one. The published trivial-test reduction transports
the complete symmetric certificates through the actual rank-one scalar
equivalence and determinant-twist induction equivalence to the original
arbitrary rank-one test representation. This retains the supplied additive
character, self-dual Haar measure, and all functional and existence
quantifiers. The helper's paired Markdown explains each comparison.

The L theorem applies `twoBlockLRankOne_of_uniform_mellin`, in
[TwoBlockModelLDivisibility](TwoBlockModelLDivisibility.md), to the published
closed theorem `uniformFiniteFunctionMellinConvergence`, imported from
`UniformFiniteFunctionMellinConvergenceProof`. This discharges its sole
analytic premise. The convergence threshold is chosen before every full
additive Schwartz–Bruhat test, supplying the genuinely common bound used
by the actual coefficient models in `ModelMatrixAnalyticData`.

The divisibility route passes through the actual induced quotient onto
the block coefficient models. Full induced Whittaker type identifies the
coefficient models, while the quotient inclusion preserves each actual
matrix rational value. Forward matrix expansion and reverse realization
on the actual upper normalized induction give the product generator.
Its span contains the normalized reciprocal generator of the induced
original's coefficient model, so the induced L polynomial divides the
product of block L polynomials. Choose `e = 0` in the required equality
`X ^ e * prod i, Pi i = Q * P`. These generator comparisons come from the
published `I1 = I3 = I2` proofs and full symmetric L-polynomial existence.
The helper's paired Markdown details every interface.

The published `twoBlockLRankOne_of_trivial_test` reduction constructs the
actual rank-one scalar equivalence and determinant-twist induction
equivalence. It transports the complete symmetric L certificates back to
the original arbitrary rank-one test representation, preserving the
supplied Haar measure and its certificate quantifiers. Both final
theorems retain independent field, test-carrier and block-carrier
universes, reducible full Whittaker-type inputs, and both positive block
ranks exactly as in their targets.

This module is an internal composition of published results in the
analytic setting of JPSS, *Rankin–Selberg Convolutions* (1983),
Theorem 3.1, printed pp. 404–405, Sections 5.3–5.4, printed pp. 422–423,
and Section 7.1(3), printed pp. 438–439. The registered source
`jpss-1983-rankin-selberg` has SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The implemented route works directly with upper normalized induction
using actual coefficient quotients and generic-socle occurrence.
It invokes no unrestricted or finite-block multiplicativity or later
Section 7 descendant.
