# Denominators of Newton polynomials of integer-valued sequences

Module `Langlands.Algebra.RationalPolynomialNewtonIntegrality`.

## Content

Recall `Langlands.Algebra.RationalPolynomial.newtonPolynomial f d`, the
truncated Newton polynomial of a sequence `f : ℕ → ℚ`:
`∑_{k ≤ d} C(Δ^k f(0) / k!) · descPochhammer ℚ k`, where `Δ = fwdDiff 1`.
Here "integer-valued" means taking values in `(Int.castRingHom ℚ).range`.

- `iterate_fwdDiff_mem_intCast_range`: if `f` is integer-valued, then so is
  every iterated forward difference `Δ^k f`.
- `factorial_mul_coeff_newtonPolynomial_mem`: if `f` is integer-valued, then
  `d! · (newtonPolynomial f d).coeff j` is an integer for every `j`.
- `factorial_mul_coeff_newtonPolynomial_sub_mem`: the same bound for the
  difference `newtonPolynomial f d - newtonPolynomial g d` of two
  integer-valued sequences.

## Proof

The forward difference `Δg(n) = g(n+1) - g(n)` of an integer-valued sequence
is integer-valued, and induction on `k` gives the first statement. For the
second, expand the coefficient as a finite sum. In the term of index
`k ≤ d`, write `d! = k! · m` (`Nat.factorial_dvd_factorial`). The term
becomes `m · Δ^k f(0) · (descPochhammer ℚ k).coeff j`. The last factor is the
image of the integer coefficient `(descPochhammer ℤ k).coeff j`
(`descPochhammer_map`). The third statement follows from linearity of
coefficients.

## Provenance

This is the standard fact that a numerical polynomial of degree at most `d`
has coefficients in `(1/d!)ℤ` (see, e.g., Hartshorne, *Algebraic Geometry*,
I, Proposition 7.3, on numerical polynomials as integer combinations of
binomial coefficients). It is stated here for the project's
falling-factorial Newton polynomials. These underlie the Euler polynomials
`coherentEulerPolynomial` and `mixedLineBundleEulerPolynomial`, whose
interpolated values are integer Euler characteristics.
