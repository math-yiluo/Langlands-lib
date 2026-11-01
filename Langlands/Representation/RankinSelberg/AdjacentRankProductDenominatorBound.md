# Product denominators for actual realized corank values

Worker 486. This internal construction supplies the ordinary denominator
membership needed after the actual adjacent-rank finite-product calculation.
It retains arbitrary full Whittaker-type second inputs, including reducible
ones, every natural rank including zero, and independent field and two
original carrier universes.

`AdjacentRankCorankDenominatorBound` says that every rational continuation of
one specified actual corank integral belongs to the Laurent span of the
reciprocal of the proposed polynomial. It includes the actual supplied
quotient measure and canonical residue cardinality and absolute value.
It is a local bound for that specified pair of functions; it does not assert
an inclusion for the entire induced zeta module.

`adjacentRankProductContinuation_denominatorBound` consumes the actual matched
product-continuation data and the actual determinant-twisted matrix witnesses.
It also consumes two complete supplied-measure symmetric L-polynomial
certificates: `P0` for the equal-rank pair `(sigma,tau)` at `psi`, and `P1` for
`(twist (chi composed with determinant) tau, rankOneCharacter 1)` at the
standard scaled character `psi.scale (-1)`. The latter is the actual twisted
second representation, without an irreducibility or original/model-equivalence
assumption. No polynomial-existence premise is silently discharged.

The first certificate supplies the normalized generator of the actual
equal-rank rational values for the supplied compatible quotient measure. The
second supplies the ordinary matrix normalized generator on the actual
coefficient model at the same transported nonzero functional, by
`isMatrixNormalizedGenerator_model_of_pair`. Full type and nonzeroness on the
twisted original are obtained by the published determinant-twist transports.
Each literal matrix function is an actual bi-smooth coefficient of that model
by `determinantTwistModelCoefficient`.

Destructing the product data gives the finite rational values `Ai`, their
continuations, a common half-plane of equal-rank convergence, and the exact
unique corank value `C(c) * sum_i Ai*Mi`. The convergence and continuations put
every `Ai` in the actual equal-rank value family. The supplied actual shifted
matrix witness puts `Mi` in the actual twisted-model matrix value family.
Thus every summand belongs to their product value family. Finite summation and
complex constant multiplication preserve its Laurent span. The published
`normalizedGenerator_productRationalValues` identifies that span with the
reciprocal span for exactly `P0*P1`. Uniqueness in the continuation data gives
the result for every rational continuation, retaining the explicit scalar
without dividing by it.

This is composition of established analytic predicates, actual coefficient
transport and Laurent-module algebra. It claims no separate literal source
theorem, factor existence, full induced-module span inclusion, arbitrary
parameter specialization, or final adjacent-rank gamma/L certificate. It uses
no later multiplicativity theorem.
