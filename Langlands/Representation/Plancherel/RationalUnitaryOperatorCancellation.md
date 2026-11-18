# One denominator after finite unitary basis-root cancellation

The primary construction is
`Langlands.Plancherel.rationalUnitaryCancelledOperator`.
This internal unit assembles algebraic cancellation for polynomial operators
on the actual unramified parameter space. A supplied list of basis-coordinate
root powers describes the factors to remove from one common denominator.
Each root direction has its own supplied integral basis of the actual
valuation image; the unit does not identify those directions with a root
system or prove any standard-family pole-support claim.

The construction and its proofs retain the existing actual regular-function
algebra and the existing finite-expansion polynomial-operator predicate.
Cleared unitary norm bounds permit a different constant for each input
vector. Scalar algebraic tests are bounded on the finite-dimensional value
span of each polynomial numerator, so coordinate-root divisibility gives
one polynomial quotient operator, linear in the input.

The finite iteration removes one prescribed power at a time and
retains the vector estimate for the new denominator. No coprimality between
successive factors is assumed. The proof extends the cleared estimate to all
unitary points by continuity, divides the polynomial operator using scalar
tests, and cancels the same factor from the estimate on its dense unitary
nonzero locus. Continuity of the quotient numerator retains the estimate at
the zeros of that factor. Induction on the supplied list constructs the one
quotient operator, its global polynomiality, its factor identity and its
remaining-denominator bound.

`rationalUnitaryCancelledQuotient` divides this polynomial operator by the
remaining scalar denominator `d` on its nonzero locus. That locus is ambient
open, and the quotient satisfies the existing whole-operator rationality
predicate with denominator `d`. If a consumer proves `d` is nonzero at every
unitary point, this single regular region contains all those points. The
module does not assert that nonvanishing condition or a denominator
factorization for any standard family.

This is a supporting algebraic step for the
root-hyperplane cancellation in Waldspurger (2003), Corollary V.2.3 and
Lemma V.3.1 (printed pp.294–295 / PDF pp.60–61, registered as
`waldspurger-2003-plancherel`). Analytic norm identities, actual pole support,
continuation existence and the closed V.3.1 theorem remain separate.
