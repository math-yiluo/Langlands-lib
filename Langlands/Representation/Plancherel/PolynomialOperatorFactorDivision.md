# Whole-operator polynomial division from scalar tests

This module isolates the vector and operator assembly needed
after scalar pole cancellation in the common-Levi V.3.1 target. Its motivation
is Waldspurger (2003), V.2.3 and Lemma V.3.1, printed pp.294–295 / PDF pp.60–61,
registered as `waldspurger-2003-plancherel`. The results below are linear
algebra consequences of the published finite polynomial expansion predicate
and continuity of regular scalar functions, rather than new analytic claims
from the source.

The parameter space is the existing group of unramified characters for an
arbitrary norm-character family. The parameter subset can be any subset.
Vector carriers are arbitrary complex vector spaces, without a topology or
finite-dimensionality hypothesis. The factor `d` belongs to the existing
regular scalar algebra.

`IsPolynomialOn.continuous_linear_test` proves continuity of every scalar
algebraic linear test of a polynomial vector family.
`polynomial_eq_of_regular_smul_eq` then proves uniqueness of polynomial
division by `d` if its nonzero locus is dense on the parameter subset. It uses
continuity of all scalar tests and separation by the algebraic dual.

`exists_polynomial_quotient_of_linear_tests` assumes a polynomial vector family
and polynomial quotients by the same `d` for every scalar linear test. It
concludes existence of a polynomial vector quotient. The proof uses the
finite-dimensional span of the finitely many numerator vectors, extends its
basis coordinate functionals to the ambient vector space by a linear left
inverse, divides those finitely many coordinates using the hypotheses, and
reassembles them in the same fixed finite span.

`exists_polynomial_operator_quotient_of_linear_tests` assumes a whole
polynomial operator family and the same scalar factor for every linear test
of every input vector. With the dense nonzero-locus hypothesis, the vector
quotients assemble to an operator family linear in the input. Each fixed
input still has a finite polynomial expansion, and the operator identity is
`N(z) = d(z) • Q(z)` at every parameter, including zeros of `d`. The proof first
chooses the vector quotients, then uses polynomial uniqueness to prove
additivity and scalar compatibility of the choice.

`polynomialOperatorFactorQuotient` constructs one such operator quotient from
the proved assembly theorem. `polynomialOperatorFactorQuotient_isPolynomial`
proves its finite polynomial expansion on each input, and
`polynomialOperatorFactorQuotient_spec` proves its exact whole-operator factor
identity at every parameter. The construction retains the same factor and
scalar-test divisibility hypotheses.

The common factor is selected before the input vector and its scalar test.
This theorem does not choose a different denominator for each vector. The
analytic proof that the particular tensor's scalar numerators have the factor,
and the proof of density needed for uniqueness, remain explicit inputs.
