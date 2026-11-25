# Smoothness of Laurent polynomials

For a commutative ring `R`, the Laurent polynomial algebra `R[T;T⁻¹]` is smooth over `R`. Mathlib identifies it with the localization of `R[X]` at powers of `X`. The polynomial algebra is smooth, localization away from one element is smooth, and smoothness is closed under composition.

The instance `LaurentPolynomial.isScalarTower_polynomial` supplies the scalar tower for that composition. It also applies over a commutative semiring and follows from the formula for the image of a constant polynomial.
