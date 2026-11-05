# Characteristic-polynomial coefficients of an integral matrix

This internal algebraic helper is derived for the anisotropic spectral integrality
proof. It concerns a finite square matrix over a field, viewed as an element of
an algebra over an arbitrary commutative ring. It assumes integrality of that
matrix element and proves integrality of every characteristic-polynomial
coefficient. No nonempty index type or faithful matrix representation is assumed.

The first lemma maps a monic annihilating polynomial to the coefficient field.
The minimal polynomial divides that mapped polynomial, and each
characteristic-polynomial root is an eigenvalue and hence a minimal-polynomial
root. It therefore satisfies the original monic polynomial.

The coefficient theorem extends scalars to an algebraic closure, applies the
root lemma to every root of the characteristic polynomial there, and uses
Mathlib's result that a split polynomial with integral roots and integral leading
coefficient has integral coefficients. Injectivity of the field embedding
descends the result. The proof uses no local-field or anisotropy assertion.
