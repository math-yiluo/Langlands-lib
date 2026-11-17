# Laurent coordinate divisibility from unitary slices

This derived algebraic unit supports the pole-cancellation step in Waldspurger
(2003), V.2.3, printed p.294 / PDF p.60, reused in Lemma V.3.1 on printed p.295 /
PDF p.61. The registered original is `waldspurger-2003-plancherel`. The source
uses density in real root hyperplanes to cancel known possible poles. This
module proves an elementary coordinate version in a finite Laurent algebra.
It does not prove pole support for an intertwining operator or identify an
actual root hyperplane with the coordinate hyperplane.

`laurent_T_sub_C_dvd_iff_eval_eq_zero` proves the factor theorem for Laurent
polynomials over any commutative coefficient ring and any unit of that ring.
The proof clears a power of the Laurent variable, applies the ordinary
polynomial factor theorem, and multiplies by the inverse Laurent monomial.

`circle_infinite_of_isOpen` proves that nonempty open subsets of the circle are
infinite, using connectedness, closedness of finite subsets, and the existing
infinitude of the circle. `finiteLaurent_eq_zero_of_eval_unitary_open` then
reduces a nonempty open subset of a finite unitary torus to a product of such
infinite subsets. The published finite Laurent identity theorem implies that a
Laurent polynomial vanishing there is zero. The zero-dimensional case is
included.

`finiteLaurentFirstEvaluation n a` evaluates the first variable at a specified
complex unit `a`, retaining the other `n` variables in their finite Laurent
algebra. `finiteLaurentEvaluation_firstEvaluation` verifies its compatibility
with simultaneous torus evaluation. `finiteLaurentCoordinateRoot n a` is the
factor `X₀ - a` transported back from the iterated Laurent presentation to the
original Laurent algebra.

`finiteLaurentCoordinateRoot_dvd_iff` identifies its divisibility condition with
identically zero algebraic restriction to the coordinate hyperplane.
`finiteLaurentCoordinateRoot_dvd_of_eval_unitary_open` assumes vanishing when
the first coordinate is `a` and the remaining unitary coordinates range over a
nonempty open set, and concludes divisibility by that factor. The parameter
`a` is any complex unit; when `a` lies on the circle, the slice is part of the
unitary torus. The proof combines the restriction identity theorem with the
Laurent factor theorem.

Passing from bounded generic tensor values to vanishing of a cleared numerator
on the required slice, changing coordinates for actual root factors, retaining
one denominator for the entire operator, and assembling the all-unitary
extension remain separate obligations.
