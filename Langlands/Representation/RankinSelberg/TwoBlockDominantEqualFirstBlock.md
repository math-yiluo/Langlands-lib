# First-block Laurent laws for actual equal-rank Jacquet coefficients

Worker 484 supplies this internal specialization of the published ordinary
Jacquet functional theorem, the first-block Laurent identity and the
unequal-rank functional equation. It discharges the first-block epsilon
premise for the original equal-rank induced coefficient model at sufficiently
large real deformation parameters. It proves no final gamma or L assertion.

The canonical p-adic field, supplied unitary additive character and supplied
self-dual Haar measure are retained. The test carrier and the dependent
block carriers have independent universes. Both block sizes are positive.
`firstBlock_lt_total` derives that the first block has smaller rank than the
total, directly from the two-block sum.

`equalFirstBlockLowerSeries` is the coefficient series of the actual published
lower unfolding integrand. Its measure is the pullback of the supplied
standard quotient measure through `lowerToStandard`, restricted to the
specified determinant slice. The original section, both block functionals,
test-model coefficient and Schwartz–Bruhat row test occur in that integrand.
No abstract replacement for the lower coefficient is introduced.

`EqualFirstBlockCoefficientLaw` is a proposition about fixed ordinary induced
and test functionals and the supplied large and first-block quotient measures.
One complex unit zeta, one epsilon unit c, one integer d and two ordinary
polynomials P and Pdual precede every section, model coefficient and row test.
They satisfy the actual small-pair epsilon equation, the minus-one model
scalar relation, and both normalized-generator predicates for every pair of
complementary rectangle dimensions j,k. The epsilon equation retains its
complete functional-equation body; the definition also exposes the generator
certificates explicitly. For the actual equal-rank slice series a of
`modelMap Ju f` and the lower series b, the law is

`Pdual(q^(-1) X^(-1)) • b = (zeta^t c X^d P) • a`.

The action is finite Laurent convolution on bilateral coefficient functions.
No general polynomial action is cancelled.

`exists_equalFirstBlockCoefficientLaw` assumes full standard Whittaker type
of the test representation and both original blocks, a nonzero test
functional and nonzero inverse block functionals, and right invariance of
the two canonical unipotent Haar measures. It takes the maximum of the
bounds supplied by `twoBlockFirstBlockLaurentIdentity` and
`twoBlockOrdinaryJacquetFunctional`. For every real parameter above that
single bound, all ordinary Jacquet integrands are absolutely integrable,
and a nonzero ordinary induced functional Ju realizes their actual Jacquet
functions at every ambient group element. These witnesses precede both
compatible quotient measures and every test.

For any such quotient measures, the proof transfers full inverse Whittaker
type to the first deformed block. It then applies
`unequalRankFunctionalEquation` to the test representation and that block,
using the supplied first-block quotient measure and self-dual Haar measure.
`exists_unequalRankEpsilonEquation_iff` supplies c,d and the genuine epsilon
equation. The published first-block Laurent theorem supplies its zeta and
polynomial witnesses. Finally `unfoldedJacquetSeries_eq` identifies the upper
radical-average series with the actual coefficient series of `modelMap Ju f`.
Thus the first-block law no longer assumes an epsilon equation or an upper
coefficient identity.

This is an internal derivation from the cited Lean theorems; no new source
translation is asserted. The imported first-block proof implements the JPSS
Section 4.7/4.9 calculation, and the ordinary Jacquet theorem implements its
convergent realization. This module does not identify the second, reversed
first-block law, prove a Fourier comparison, extract a finite numerator,
continue in the deformation parameter, or construct induced symmetric factor
certificates. The equal-rank restriction is intentional; strict rank is a
separate argument. No induced Whittaker-type assumption or irreducibility
assumption is added.
