# Determinant-slice expansion of the actual unequal-rank integrals

Author: Worker 1037.

This module is derived internal material for the first-block Laurent proof of JPSS
(1983), Sections 4.7–4.9. It concerns the published unequal-rank integral
`unequalRankIntegral ψ abv j k μ ν W W' s`, in which the rectangular variable is
integrated first. Here `μ` is any measure on the Borel structure of the quotient
`N_(n+1) \ GL_(n+1)`, and `ν` is any measure on the rectangular matrices.

`unequalRankSliceCoefficient T j k ψ μ ν W W' m` is the restricted integral over
the determinant slice `m` of the inner rectangular integral of the integrand at
`s = 0`. The weight used is the normalized absolute value of `T`.

`unequalRankIntegrand_eq_mul_spectralPoint_zpow` proves the following identity on
slice `m`. The integrand at `s` equals its value at `0` times
`spectralPoint q s ^ m`, where `q` is the residue cardinality. The proof uses
additivity of the complex exponent in the determinant weight, and the published
identity that expresses the normalized determinant weight as a power of the
spectral point.

`unequalRank_sliceExpansion` assumes absolute convergence `UnequalRankConverges` at
one parameter `s` on the product measure, with both measures s-finite. Under this
hypothesis the inner integral at `s` is integrable on the quotient. The published
partition of the quotient into determinant slices then gives two conclusions:

- the series `Σ_m a(m) (q^(-s))^m` of the slice coefficients is absolutely
  summable;
- the series has sum the actual integral at `s`.

No support bound, continuation or functional equation is used.
