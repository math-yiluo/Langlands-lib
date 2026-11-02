# Strict-rank symmetric factors and the real-ray L bound

This internal deduction extends the retained strict-rank rational comparison to
one common real opposite-twist bound, identifies its block witnesses with full
symmetric factors, and proves the symmetric L divisibility bound for the actual
lower induction. The field, test carrier and block carriers retain independent
universes. Full Whittaker type permits reducible representations.

The module translates no new assertion from the literature. It composes the
strict first-block, reversed-dual and finite-numerator constructions with
published unequal-rank analysis, symmetric factor existence and normalized
generator uniqueness. The generic identification lemmas are imported from
`TwoBlockDominantEqualFactors`; those lemmas allow arbitrary strictly unequal
ranks and do not assume equality of the total and test ranks. No unrestricted
multiplicativity theorem is used.

The closed proposition `TwoBlockDominantFirstBlockLaurentIdentityStatement`
remains an explicit hypothesis `H` in both real-ray existence theorems. Its
independently owned proof is not discharged here. The fixed-model comparison
and identification theorems instead take their retained actual certificates
explicitly.

`exists_strictTwoBlockRationalComparison` starts with `t < r`, full test and
base-block type, nonzero test and inverse block functionals, and the supplied
self-dual Haar measure. The common-bound finite-numerator theorem supplies
one real bound. For every larger real opposite twist it supplies absolute
ordinary Jacquet convergence, a nonzero functional realizing that exact
Jacquet integral for every section and group element, and finite numerators
for every choice of compatible total and block quotient measures.
`strictTwoBlockRationalComparison_of_numerators` then supplies the actual
original and reversed rational continuations, their rational reflection
identity, all retained block certificates, finite model clearing and the
intrinsic normalized-generator bound at every complementary row pair. The
same bound and Jacquet functional are retained. The functional precedes all
three quotient measures; polynomial and epsilon witnesses precede every
complementary row and coefficient test. The additive measure is unchanged.

`StrictFirstBlockSymmetricFactors` packages the symmetric epsilon certificate,
the original symmetric L certificate, the inverse-transpose symmetric L
certificate at the negated character, and the symmetric gamma certificate for
`rationalGammaExpression (residueReflection F) c d P Pdual`. This definition
is meaningful for the ranks carried by its representations; its use below is
strictly dominant. `StrictFirstBlockFactorCertificate.symmetricFactors` applies
`symmetricFactors_of_modelCertificates` to the retained epsilon equation and
the original and dual model generators. The two positive block sizes give
`m 0 < t`, and `t < r` gives the needed strict block/test inequality. It keeps
the same epsilon coefficient, exponent and both polynomials. The retained
central minus-one scalar is not needed for this identification.

The imported generic identification uses uniqueness against a full symmetric
L polynomial to promote a model generator to the complete certificate. It
uses the actual dual rational-value identity for the second polynomial,
compatible quotient Haar uniqueness for the epsilon equation, and the
published Whittaker-type construction input for gamma. Consequently the
conclusions contain the existence witnesses and every measure and functional
quantifier of the full symmetric predicates; they are not certificates for
only the displayed model or supplied quotient measure.

`StrictTwoBlockSymmetricLBound` asserts full symmetric L certificates for the
actual lower induction and its two original blocks, with polynomial witnesses
`Q` and a natural exponent `e` satisfying
`X ^ e * (P₁ * P₂) = Q * P`.
`strictTwoBlockSymmetricLBound_of_rationalComparison` proves this from the
actual strict rational comparison, full test and block type, nonzero test and
block functionals, and compatible total and two block quotient measures.
The first retained certificate gives the original first-block polynomial
`P₁`. The reversed certificate has original polynomial `P₂D` and dual
polynomial `P₂`. Its dual symmetric L certificate becomes the certificate for
the actual second block by double negation of the character and involutivity
of inverse transpose. No factor polynomial is replaced.

Full type of the actual lower induction follows from
`lowerInduced_inverseWhittakerType` and standard/inverse character equivalence.
`symmetricLPolynomialExists` supplies a whole-pair symmetric L polynomial `P`.
Its specialization to the compatible total quotient measure is a pair L
polynomial. Since `t < r`, `isPairLPolynomial_of_lt` specializes it at
`j = 0`, `k = r - t - 1`. The rational comparison's intrinsic bound at this
rectangle supplies exactly the displayed equation with the same retained
`P₁` and `P₂`. This preserves the required divisibility direction.

`exists_strictTwoBlockSymmetricLBound` assumes `H`, `t < r` and full standard
Whittaker type of the test and base blocks. It chooses nonzero functionals
from full type, constructs right-invariance instances, obtains the preceding
common-bound rational comparison, and specializes it at the canonical
compatible total and block quotient measures. At every larger real parameter,
full type of the opposite-twisted blocks follows from twist invariance, so the
fixed-model theorem gives the symmetric L bound. Functional nonvanishing,
quotient compatibility, induced full type and the actual finite-numerator
and rational identities are discharged internally in this existence theorem;
`H` remains explicit.

The result concerns the actual lower induction for sufficiently large real
opposite twists. It does not supply the whole-pair gamma product, continuation
to zero, transport to the upper induced representation, or either final
closed dominant-rank target.
