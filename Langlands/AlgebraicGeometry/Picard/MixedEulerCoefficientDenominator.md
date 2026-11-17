# Bounded denominators of actual mixed Euler coefficients

Module `Langlands.AlgebraicGeometry.Picard.MixedEulerCoefficientDenominator`.

## Content

Fix a field `K`, a proper morphism `f : X ⟶ Spec K` and line bundles `L`,
`N` on `X`. The Library defines `mixedLineBundleEulerPolynomial f L N d`
as the difference of two degree-`d` truncated Newton polynomials. The first
interpolates `n ↦ χ(N ⊗ L^n)` and the second interpolates `n ↦ χ(L^n)`.
Both use actual coherent Euler characteristics. The Library also defines
`mixedLineBundleEulerCoefficient f L N d` as the coefficient of index `d - 1`
of this polynomial.

- `coherentEulerSequence_mem_intCast_range`: every value of the actual
  twisted Euler sequence `coherentEulerSequence f M hM L` is an integer. By
  definition it is the cast of an integer Euler characteristic.
- `factorial_mul_mixedLineBundleEulerPolynomial_coeff_mem`: for every `j`,
  `d! · (mixedLineBundleEulerPolynomial f L N d).coeff j` is an integer.
- `exists_int_factorial_mul_mixedLineBundleEulerCoefficient`: there is an
  integer `z` with `d! · mixedLineBundleEulerCoefficient f L N d = z`.

## Proof

The two interpolated sequences are integer-valued, so the second statement
is `factorial_mul_coeff_newtonPolynomial_sub_mem` from
`Langlands.Algebra.RationalPolynomialNewtonIntegrality`. The third statement
specializes it to `j = d - 1`.

## Provenance

Internal bookkeeping fact. In the abelian-variety application, `d` is the
dimension `g` and the coefficient is the mixed intersection number
`(L^{g-1} · N)/(g-1)!` of the Riemann–Roch expansion (Mumford, *Abelian
Varieties*, §16). Only the crude bound "denominator divides `g!`" is
recorded here, and it is proved from integrality of Euler characteristics
alone.
