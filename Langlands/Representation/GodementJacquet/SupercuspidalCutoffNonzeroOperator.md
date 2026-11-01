# Nonzero Fourier-regular matrix zeta operators

This derived helper uses the actual coefficient cutoffs, their proved Fourier
regularity and the actual regular-test zeta operator. Pointwise complex
conjugation preserves Schwartz–Bruhat matrix tests. Its raw plus Fourier
transform at a matrix is the complex conjugate of the original transform at
the negative matrix, by unitarity of the supplied additive character and
conjugation of the actual scalar integral. Both singular-vanishing conditions
are therefore preserved.

For a supercuspidal representation of dimension parameter `m+1`, with `m>0`,
let a smooth algebraic functional and a vector have nonzero pairing. The
complex conjugate of their determinant-unit coefficient cutoff is an actual
Fourier-regular test. Evaluation of its zeta operator on that same vector and
functional is the integral of the squared absolute value of the cutoff.
The determinant weight is exactly one on the norm-one shell at every complex
exponent, and the cutoff vanishes elsewhere. The squared absolute value is
continuous, compactly supported on GL, nonnegative and nonzero at the identity.
Open positivity of the shared normalized Haar measure makes its integral
strictly positive. Consequently this single test has a nonzero actual zeta
operator at every exponent.

For any nonzero vector in a smooth representation of canonical p-adic GL,
`exists_smoothFunctional_ne_zero` obtains a smooth algebraic functional with
nonzero pairing. The actual compact-open subgroup construction gives cofinality
inside each open subgroup. The published injectivity of the smooth bidual
then separates the vector. Choosing a nonzero vector gives
`exists_fourierRegular_nonzero_zetaOperator_of_nontrivial`: every nontrivial
supercuspidal representation at rank `m+1`, with `m>0`, has one such test,
without supplying a smooth functional as an additional premise.

The field and representation-carrier universes remain independent. The
additive character and scalar self-dual measure are supplied unchanged.
No invariant positive form or unitarization premise is used. This helper
does not yet assert the functional equation, scalar gamma factor, or
realization of every finite-rank operator.

Explicit module-specific names for the canonical local instances allow this
helper to be imported together with matrix analytic data and Fourier transport.
The instance bodies, test construction and nonvanishing proofs are unchanged.
