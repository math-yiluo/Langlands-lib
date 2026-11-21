# The continued Godement value and the complex Jacquet quotient recursion

`ComplexGodementRecursionComparisonStatement` compares two evaluations on
\(\mathrm{GL}_{m+1}(\mathbb C)\), where \(m=r+1\). The smaller coefficient is
continuous and satisfies the Whittaker law with parameter \(-a\) and
`HasSimpleRootLogBound`. The continued Godement integral uses the group
Haar measure supplied by `D` and the scalar self-dual measure for \(a\).
For every shift \(s\) of the adjoining exponent and every larger group
argument, its value is the quotient recursion with parameter \(-a\) and the
shifted inducing character, multiplied by \(d((-1)^m)\).

`continuedValue_eq_signed_recursion` uses the positive partial Fourier
transform of the right-translated rectangular test. At the augmented point
of a smaller matrix \(h\), this equals the last-column Fourier integral at
\(h\) and the last row of \(h^{-1}\). The normalized absolute value is the
square of the complex norm, so shifting the inducing exponent by \(s\)
incorporates exactly the additional determinant power, both in the inner
kernel and at the larger group argument. The resulting integrand agrees
pointwise with the recursion group kernel at \(h^{-1}\). The smaller general
linear group's Haar measure is invariant under inversion. The existing
fixed-parameter convergence theorem identifies the resulting group integral
with the quotient recursion.

This internal comparison connects the Library's continued Godement value with
the quotient formula in Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
§7.2, formula (7.7) on p. 48 and formula (7.8) on p. 50. Formula (7.8)
omits the inner determinant modulus in print. In Jacquet's coordinates the
Lean weight is \(\mu_n(\det h)|\det h|_{\mathbb C}^{u_n+n/2}\). This is the
weight in (7.6) on p. 48, preserved by \(h\mapsto hv\) since \(v\) is
unipotent. The first display for the dual coefficient in the proof of
Proposition 7.3 on p. 51 also includes the modulus. The factor \(d((-1)^m)\)
is the upper-Borel normalization used in `continuedValue`.
