# Regularity of Euler denominators for unitary operators

This internal derived result concerns the published determinant Euler polynomial
`Langlands.LocalFactor.eulerPolynomial`. A complex endomorphism of a
finite-dimensional vector space preserves a supplied positive definite Hermitian
form. Its Euler polynomial is nonzero at every complex number whose norm differs
from one. No topology or norm on the vector space is assumed.

The Lean proof rewrites polynomial evaluation as the determinant of `1 - z A`.
If that determinant vanishes, its kernel contains a nonzero vector `v`, giving
`v = z A v`. Form preservation and sesquilinearity imply that the nonzero scalar
`h(v,v)` equals `norm(z)^2 h(v,v)`. Cancellation and nonnegativity of the complex
norm force `norm(z) = 1`, contradicting the point's hypothesis.

`regularPointOfPreservesPositiveForm` packages this nonvanishing in the existing
`RegularPoint` subtype. The spectral lemmas compute the norm of the published
parameter `exp(-s log q)` as `exp(-Re(s) log q)`. For `q > 1`, the real logarithm
is positive, so the norm can equal one only when `Re(s) = 0`. The definition
`spectralRegularPointOfPreservesPositiveForm` therefore packages each `s` with
nonzero real part in the existing `SpectralRegularPoint` subtype. These
constructions retain the supplied operator, complex point and spectral parameter.
The vector-space universe is unrestricted.

The provenance is elementary finite-dimensional linear algebra derived for the
arithmetic local-factor bridge in Henniart's induction argument. This lemma uses
only the actual determinant operator and a positive form; it does not assert
existence of a form or any automorphic local-factor identity.
