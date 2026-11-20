# Continuation from normalized Rankin–Selberg tests

`regularizeSimplePoles` multiplies an integral by `s * (s - 1)` and fills
removable singularities using Mathlib's meromorphic normal form. For a function
holomorphic off `0` and `1` with order at least `-1` at both points, its
regularization is entire. The regularized value is nonzero at either point
exactly when the corresponding order of the original function is negative.

`exists_continuation_of_normalized_tests` takes a family of these test
integrals and entire normalized factors with no common zero. Each integral
is the corresponding normalized factor times the initial product on a
right half-plane. The threshold can depend on the integral. After clearing
the two possible poles, cross multiplication on the overlap of any two such
half-planes gives an identity of entire functions. A test whose factor is
nonzero at a point gives an analytic quotient there. The cross identities
make these local quotients agree and imply that every cleared integral is the
product of its normalized factor and the resulting entire function.

One fixed test with a nonzero normalized factor somewhere is enough to
recover the initial product wherever this factor is nonzero in its
convergence half-plane. Continuity of the initial product on a right half-plane
extends the agreement to the isolated zeros of the fixed factor. Dividing the
entire function by `s * (s - 1)` recovers a continuation. It has a pole at
`0` or `1` precisely when some test integral has a pole there. The hypothesis on
this family of pole orders gives `HasSimplePoleProfile`.

`isBoundedInVerticalStrips_of_normalized_sum` supplies the strip-bound
transfer when a fixed finite linear combination of normalized factors is
identically one off the two possible poles. The same linear combination of
integrals equals the continuation there. The sum of their strip bounds
weighted by the norms of the coefficients bounds the continuation.

This is the analytic step in J. W. Cogdell, *Analytic theory of L-functions
for GL_n* (2004), §4.1, pp. 219–221, and §4.2, p. 222, ending at Theorem 4.2.
The registered source `cogdell-2004-analytic-theory-gln` has these passages on
PDF pp. 222–225, with SHA-256
`8117f145869274324b12344dc83fa3289e3bd27c515b8d0d4a0211cd64174944`.
The module makes the analytic argument explicit for any test family with the
specified factor identities, right-half-plane continuity and local nonvanishing.
