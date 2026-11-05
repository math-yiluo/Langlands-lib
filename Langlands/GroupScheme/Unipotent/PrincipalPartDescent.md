# Galois descent of additive principal forms

Author: Worker 864.

This module implements the Galois-descent argument of Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), Lemma B.1.8, printed
p.564, one-based PDF p.590, and the polynomial input to B.1.9, printed
p.565, one-based PDF p.591.
The registered source is `conrad-gabber-prasad-2015-pseudo-reductive`,
SHA256 `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.

`HasAnisotropicPowerSum p c m` says that
`∑ i, c i * b i ^ (p ^ m i)` vanishes only at the zero vector.
The coefficient field, extension field, and finite index type have
independent universes. In the preservation theorem `p` is the exponential
characteristic of the coefficient field: this includes positive
characteristic as in CGP, and characteristic zero with `p = 1`.
The Galois extension is algebraic and may have infinite degree.

The proof uses strong induction on a finite set containing the support
of an extension-field zero. Choose a coordinate of maximal exponent in
that set. If it is zero, erase it and invoke induction. Otherwise divide
each coordinate by a suitable power of the chosen nonzero coordinate,
so the chosen coordinate becomes one and the whole equation is divided
by a common power. The difference between this normalized zero and any
Galois conjugate has a smaller support. Induction makes that difference
zero. The fixed-field theorem then descends every normalized coordinate
to the coefficient field, where anisotropy contradicts the coordinate
equal to one.

The implementation chooses the maximal exponent explicitly, so every
exponent difference used in normalization is nonnegative. This avoids
relying on the ordering of coordinates in the printed normalization
formula.

This is a polynomial input. It does not construct presentations of
arbitrary unipotent groups or prove the woundness criterion.

`exists_nonzero_powerSum_zero_iff_of_isGalois` states the existence
version directly. Its extension-to-base direction is the contrapositive
of anisotropy preservation. The base-to-extension direction maps the
coordinates through the injective field map. The result includes zero
coefficients and the empty finite index type.

`HasAnisotropicPrincipalPart.map_of_isGalois` applies preservation to
the already published polynomial principal-part predicate. It assumes
an explicit family of nonnegative integers `m` such that the degree of
coordinate `f i` is `p ^ m i`. Injectivity of the coefficient map preserves
each degree and leading coefficient. This adapter does not assume that
the polynomials are additive; only the shape of their degrees is needed.
It does not assert the other geometric equivalences in B.1.7–B.1.9.

The internal predicate packages anisotropy for this proof. Its provenance
is derived from the zero condition in B.1.8. The characteristic-zero
case is an extension of the printed positive-characteristic result:
all relevant powers are first powers, and the same induction applies.
