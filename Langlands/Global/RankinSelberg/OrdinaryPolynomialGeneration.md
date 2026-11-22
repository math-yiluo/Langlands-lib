# Polynomial normalized values and finite generation

`ordinaryPolynomialGeneration` proves the algebraic step from pointwise
coverage by polynomial normalized values to a finite sum equal to one.
The span must be closed under multiplication by the spectral variable,
and scalar multiples of a test polynomial must occur as test polynomials.

Closure under the variable gives closure under multiplication by any
polynomial, using monomials and linearity. The span is then a principal
ideal of the complex polynomial ring. Any root of its generator is a
common root of the test polynomials, so pointwise coverage forces the
generator to be a nonzero constant. Expand one in the span as a finite
linear combination of test polynomials and absorb each scalar in a test.
Evaluation gives the required identity of entire normalized values.

This is a derived algebraic step in Jacquet, *Archimedean Rankin–Selberg
integrals* (2009), §15, author pp. 108–109, in the proof of Theorem 2.7.
The hypotheses specify the polynomial tests and their closure for the
particular local integral family to which the result is applied.

For the ordinary complex equal and unequal integrals, the two
`isOrdinaryNormalizationPolynomial` lemmas realize the scalar clause by
multiplying the first Whittaker vector by the scalar. The raw integral
and its normalization both acquire that scalar, with the remaining
test data fixed.
