# Integral homogeneity of the spherical Whittaker polynomial

This is a derived algebraic implementation of the homogeneity assertion in
Jacquet, *A correction to Conducteur des représentations du groupe linéaire*
(2012), Section 2, printed p. 520. It uses the explicit Schur formula and the
symmetric Laurent polynomial function in `Conductor.SphericalPolynomial`.

For a finite coordinate type `σ` and a field `K`, `torusPolynomialScale σ K c`
is the `K`-algebra endomorphism of the actual localized polynomial ring sending
each coordinate `X i` to `c * X i`, for a unit `c : Kˣ`. The product of the
scaled coordinates is a unit, so the localization universal property supplies
the endomorphism. It commutes with coordinate permutations and therefore
restricts to `symmetricTorusScale` on the symmetric Laurent subalgebra.
Evaluation of the scaled element at a unit tuple `x` equals evaluation of the
original element at the tuple `fun i => c * x i`.

`IsSymmetricTorusHomogeneous σ K p d` means that this scaling sends `p` to
`c ^ d * p` for every `c : Kˣ`, with the scalar embedded by the algebra map.
The degree `d` is an integer; negative degrees use powers of units.

The scalar identities are proved first over an arbitrary field. Every monomial
in a complete homogeneous symmetric polynomial of index `k` has degree `k`.
The published negative-index-zero convention extends this identity to all
integer indices. In the Jacobi–Trudi matrix for a weight `a`, scaling introduces
row factors `c ^ (a i - i)` and column factors `c ^ j`. Factoring them out of
the determinant gives `c ^ (sum a)`, since the index contributions cancel.
For an integral weight `lam`, the additional determinant-coordinate twist in
`satakeSchur` restores the degree `sum lam`. This last identity is stated for
complex unit tuples, matching the imported scalar definition.

Evaluation separation over the infinite field `ℂ` lifts the scalar Schur
identity to `symmetricTorusSchur`. Consequently,
`sphericalWhittakerPolynomial hϖ θ q g` is homogeneous of degree
`sum i, Iwasawa.exponent hϖ g i`. Its scalar unipotent and half-modulus factors
are fixed by the endomorphism; off the dominant cells the value is zero.
This identity uses the chosen Iwasawa exponents and holds for the same valued
field, uniformizer, character and natural parameter `q` as the defining
formula. It requires no additional topology or characteristic assumption.

Jacquet states the degree using the determinant norm. This unit establishes
the degree in Iwasawa exponent coordinates; it does not assert a new
comparison with a determinant norm, principal-series Whittaker realization,
compact-set finiteness, an integral transform, or the essential-vector and
conductor conclusions. These remain separate obligations of the host proof.
