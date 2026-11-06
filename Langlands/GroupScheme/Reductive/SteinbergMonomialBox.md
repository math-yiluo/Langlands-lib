# Divided polynomial coefficients and Steinberg monomial boxes

This derived algebraic unit concerns actual multivariate polynomial spaces over
an arbitrary field. Variables may lie in a separate universe and need not form
a finite type. A finitely supported exponent vector `N` defines the submodule
`monomialBox N` of polynomials supported on the finite lower interval below `N`.
Its dimension is the product of `N(i)+1` over the support of `N`.

`dividedPower a` is a linear endomorphism defined on the monomial basis by
`X^b ↦ (∏ i in support(a), choose(b(i),a(i))) X^(b-a)`. This is the explicit
multivariate divided polynomial derivative; subtraction is coordinatewise
truncated subtraction. If an index exceeds its monomial exponent, its binomial
coefficient vanishes. No ordinary derivative or factorial division is used.

When all binomial coefficients from the top exponent `N` are nonzero, any
submodule containing the divided derivatives of `X^N` contains the whole box.
For each exponent `m ≤ N`, use the derivative at `N-m`. It is a nonzero scalar
multiple of `X^m`, and multiplication by the inverse scalar puts `X^m` in the
submodule. The monomial spanning description finishes the containment.

In prime characteristic, if every positive exponent of `N` equals `p^r-1`,
the existing rank-one alternating-binomial calculation proves nonvanishing
of each factor. Thus the preceding containment applies to Steinberg boxes.
The range corollary gives the corresponding dimension lower bound for any
finite vector space mapping linearly to the polynomial space.

All results are derived from the Mathlib monomial basis, finite support
submodules and finite lower-interval cardinality, elementary linear algebra,
and the Library's proved Steinberg binomial identity. There is no external
source assertion. This unit supplies no root coordinates, polynomial
restriction identity, translation or group-action comparison, or witness of
the required derivative membership. It does not prove the support bound or
irreducibility of an entire covariance space, and does not establish the
universal Steinberg big-cell statement.
