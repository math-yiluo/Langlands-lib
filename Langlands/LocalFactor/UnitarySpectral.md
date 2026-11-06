# Spectral reciprocals of operators preserving a positive form

This derived helper retains the determinant polynomial of the actual
finite-dimensional complex endomorphism, its arbitrary carrier universe, and
the existing spectral variable `exp(-s log q)`.

`spectralDenominator` is the original Euler polynomial evaluated at that
variable. It is analytic everywhere, since the exponential and polynomial
evaluation are analytic. When the endomorphism preserves a supplied positive
definite Hermitian form and `q > 1`, the denominator is nonzero at `s = 1`.
`spectralReciprocalOfPreservesPositiveForm` therefore constructs the published
`ReciprocalEntire` object with exactly this denominator.

The identity theorem for the nonzero entire denominator gives its nonvanishing
on a punctured neighborhood of every point. Its meromorphic order is thus
finite and nonnegative. The reciprocal's order is its negative and is
nonpositive everywhere. Values at denominator zeros remain represented by
punctured germs, in accordance with `ReciprocalEntire`.

This is elementary analysis of a supplied positive form. It asserts neither
existence of such a form for an automorphic representation nor an identity of
arithmetic and automorphic gamma factors.
