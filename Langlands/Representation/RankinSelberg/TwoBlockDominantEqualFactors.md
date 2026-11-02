# Symmetric identification of the retained equal-rank block factors

This internal deduction identifies the polynomial and epsilon witnesses retained
by `EqualFirstBlockFactorCertificate` with the full symmetric factor
certificates. It then proves the symmetric L divisibility bound for the actual
equal-rank lower induction at every sufficiently large real opposite twist.
The field and the two representation carriers retain independent universes.

The module composes published analytic, factor-existence and model-comparison
results. It translates no new assertion from the literature. Its source route
is inherited from the actual first-block, reversed-dual, finite-numerator and
rational-comparison constructions: the smaller-pair functional equation and
the JPSS Section 4 opposite-support argument. It uses no unrestricted
multiplicativity theorem.

`symmetricLPolynomial_of_modelGenerator` starts with a pair of full
standard Whittaker-type representations in strictly unequal ranks, nonzero
standard and inverse-standard functionals, a compatible quotient measure, and
one normalized generator for the actual model rational values at one
complementary rectangle. It obtains a full symmetric L polynomial from
`symmetricLPolynomialExists`. At the supplied measure and rectangle,
`unequalRankAnalytic` and
`UnequalRankAnalyticAt.isNormalizedGenerator_iff` identify this polynomial as
another normalized generator of the same actual model values. Uniqueness
identifies the two polynomials. The resulting certificate includes the
compatible-measure existence witness and quantification over all compatible
quotient measures; these are inherited from the full existence theorem.

`symmetricFactors_of_modelCertificates` additionally retains an actual unequal
rank epsilon equation and original/dual normalized generators at every
complementary rectangle. The first lemma identifies the original polynomial.
For the dual polynomial, `dualUnequalRankRationalValuesAt_eq` exchanges the two
rectangles and identifies the actual inverse-transpose model family.
`firstDualFunctional_ne_zero` and `secondDualFunctional_ne_zero` preserve
nonvanishing. Full type at the negated additive character follows from the
published dual-type lemmas and standard/inverse character equivalence. The
supplied additive measure remains unchanged and is self-dual for that negated
character by `negatedSelfDualHaar`.

Uniqueness of compatible quotient Haar measures rewrites the original epsilon
equation at the canonical quotient measure.
`unequalRankEpsilonFactor_of_equation` upgrades that very monomial to the
universal epsilon certificate. The construction input from
`padicPairGammaConstructionInput_of_whittakerType` and
`IsPadicPairEpsilonFactor.gammaFactor_of_constructionInput` give the symmetric
gamma certificate for
`rationalGammaExpression (residueReflection F) c d P Pdual`.
No replacement epsilon coefficient, exponent or polynomial is chosen.

`EqualFirstBlockSymmetricFactors` packages these four certificates for the
first block: epsilon, original L, inverse-transpose L at the negated character,
and gamma. `EqualFirstBlockFactorCertificate.symmetricFactors` proves this
package from the retained actual certificate. The two positive block sizes
give `m 0 < t` by `firstBlock_lt_total`. The retained central minus-one scalar
is not needed for this identification; it remains in the original certificate.

`EqualTwoBlockSymmetricLBound` asserts that the actual lower induction and its
two original blocks have full symmetric L polynomials `P`, `P₁`, `P₂`, with
polynomial witnesses `Q` and a natural exponent `e` such that
`X ^ e * (P₁ * P₂) = Q * P`.
`equalTwoBlockSymmetricLBound_of_rationalComparison` proves it from the actual
rational comparison, full test/block type, nonzero test and block functionals,
and the compatible total and two block quotient measures. The original
first-block certificate gives `P₁`. The reversed certificate has original
polynomial `P₂D` and dual polynomial `P₂`; its dual L certificate reduces to the
original second block by involutivity of inverse transpose and double negation
of the additive character. A whole-pair symmetric L polynomial is obtained
from full type of the actual lower induction. Its specialization to the
supplied compatible total quotient measure is an intrinsic equal-rank L
polynomial, so the rational comparison's intrinsic bound gives exactly the
displayed equation with the same two retained block polynomials.

`exists_equalTwoBlockSymmetricLBound` has only full standard Whittaker-type
test and base block representations as mathematical premises, in addition to
the canonical p-adic field, two-block rank equation, character and supplied
self-dual Haar measure. It chooses nonzero functionals from full type,
constructs the three right-invariance instances, and specializes
`exists_equalTwoBlockRationalComparison` at canonical compatible quotient
measures. For one real bound and every larger real opposite-twist parameter,
it applies the preceding identification to the actual twisted blocks and
ordinary Jacquet functional. Thus functional nonvanishing, measure
compatibility, first-block laws, rational comparison and induced full type
are discharged inside this existence theorem.

The result is an equal-rank statement for sufficiently large real opposite
twists and the actual lower induction. It does not establish the induced
gamma product, continuation to arbitrary deformation parameters, the strictly
dominant case, or either final dominant-rank target. Full type throughout
allows reducible representations.
