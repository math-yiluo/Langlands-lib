# Simple-root bounds for canonical complex Jacquet coefficients

`ComplexJacquetCanonicalBoundsStatement` applies to the canonical Jacquet
family attached to a compact-finite profile, a scalar additive Haar measure,
and a Fourier parameter \(a\). At every inducing parameter its group slice is
continuous, transforms on the left by the Whittaker character for \(-a\),
and satisfies `HasSimpleRootLogBound`.

The canonical continuation supplies continuity, left covariance, and a
locally uniform estimate in its Iwasawa coordinates. The trace character of
the simple-entry sum is the same Whittaker character as in the covariance
formula. To obtain the pointwise torus estimate, the proof evaluates the
uniform estimate at the center of its parameter ball and at the product of
a positive diagonal and a unitary matrix. The Iwasawa logarithms of that
product are the supplied diagonal logarithms. The sum of their absolute
values splits into the sums of the positive and negative parts, and the
simple-root sums agree. A natural decay order at least as large as the
requested real order gives the estimate because the simple-root sum is
nonnegative.

This internal comparison supplies the coefficient hypotheses used in the
Library implementation of the quotient recursion. The underlying Jacquet
continuation and passage to the quotient formula are in Jacquet,
*Archimedean Rankin–Selberg integrals* (2009), §7.2, pp. 47–50.
Proposition 7.2 starts on p. 48 and formula (7.8) appears on p. 50.
The simple-root gauge is given in (3.3) on p. 11, and Proposition 3.3 on
p. 20 gives the estimate for standard families.
