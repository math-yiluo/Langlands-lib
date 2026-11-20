# Vertical-strip bounds from finite normalized sums with bounded weights

`HasBoundedNormalizedSum` records a finite weighted combination of a
family of normalized test values equal to one on the complement of
`{0, 1}`. Each weight is bounded on vertical strips outside any fixed
open discs about those two points. Products of such families admit the
same kind of combination. The proof multiplies the local identities and
expands the product of sums over the tuples of local test indices.
Each new weight is a product of bounded weights.

At a finite place the reciprocal-combination identity for the Laurent
span supplies a weighted normalized sum. Each evaluated Laurent
coefficient has the required strip bound. Once the normalized test
integrals are known to be multiples of the completed L-function, a
finite weighted sum of their bounds gives the corresponding bound for
the completion. The Lean proof applies the constant-sum criterion to
the integrals and normalized factors after multiplication by the
weights.

This is a derived form of the strip argument in J. W. Cogdell,
*Analytic theory of L-functions for GL_n* (2004), §4.1, printed
pp. 220–221 (PDF pp. 223–224), where local tests express the L-function
using global integrals. The finite-place input is the fractional ideal
of H. Jacquet, I. I. Piatetski-Shapiro, and J. A. Shalika,
*Rankin–Selberg convolutions* (1983), Theorem 2.7(ii), printed
pp. 390–391 (PDF pp. 25–26). When archimedean local tests give a finite
sum by Jacquet's Theorem 2.7 in equal or adjacent ranks, their weights
can be taken to be constant. The transfer still requires the actual
products to be realized by global tests.
