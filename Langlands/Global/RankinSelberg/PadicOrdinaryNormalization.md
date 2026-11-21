# Normalization for each specified ordinary p-adic test

Given a rational continuation in a zeta span with specified normalized
L-polynomial, `ordinaryNormalizationOfRationalContinuation` evaluates its
cleared Laurent numerator at the spectral unit. The result is entire,
agrees with the ordinary integral after multiplication by the local
L-factor on a right half-plane, and is bounded on closed vertical
strips. These facts use the published spectral evaluation identity and
the compact-annulus bound for Laurent evaluation.

The two coefficient-model theorems use the published JPSS rationality
and convergence results for the canonical quotient measure. The
rational continuation of the specified test belongs to the actual zeta
value set. Its certified p-adic pair L-polynomial is the normalized
polynomial for that set. This gives the entire normalization for each
supplied test, including a test chosen independently to detect a global
residue. The equal-rank theorem takes a Schwartz–Bruhat test, and the
unequal-rank theorem uses the ordinary block with no rectangular rows.

The local source is H. Jacquet, I. I. Piatetski-Shapiro, and J. A.
Shalika, *Rankin–Selberg convolutions* (1983), Theorem 2.7(i)–(ii),
printed pp. 390–391 (PDF pp. 25–26). J. W. Cogdell, *Analytic theory of
L-functions for GL_n* (2004), Theorem 3.1 and the following two
paragraphs, printed p. 213 (PDF p. 216), describes this normalization
of the ordinary local integral. The Lean proof obtains it by clearing
the rational denominator and evaluating the result.
