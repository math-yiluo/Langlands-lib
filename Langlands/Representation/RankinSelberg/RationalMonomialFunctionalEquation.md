# Rational identity of a Laurent monomial functional equation

This internal consequence of the published normalized functional equation uses
only the actual rational functions and their guarded evaluation. It does not
assert analytic continuation or existence of a functional equation.

`spectralReflectionUnit` is the nonzero complex scalar `q⁻¹`. For `q>1`, a
normalized functional equation with both polynomials one gives the rational
identity obtained by substituting `q⁻¹/X` into its dual rational function. The
other side is the genuine Laurent monomial unit `c*X^m` times the original
rational function.

The proof removes the finitely many roots of the original reduced denominator
and the reciprocal preimage of the dual reduced denominator roots from an
infinite set of real spectral points. Reciprocal division is injective, and
`q>1` makes the real spectral map injective, so the remaining set is infinite.
At every remaining point, the supplied two denominator guards apply. Regular
rational substitution and multiplication identify the guarded functional
equation with equality of evaluations of the two rational functions. The
published infinite-set rational uniqueness theorem then gives the identity.

The constant and exponent conventions are exactly those in
`NormalizedFunctionalEquation q 1 1 1 c 0 m R RDual`. This derivation supplies
an algebraic input to later denominator cancellation; it supplies neither
Fourier witnesses nor matrix analytic assertions.
