# Euler polynomials of tensor products

Supporting module of the gamma comparison for weakly associated cuspidal pairs,
`AssociatedGammaStatement` (module `Langlands.Automorphic.AssociatedGammaTensorEuler`,
namespace `Langlands.Automorphic.Unramified`). At finite places where a weakly associated pair
is unramified, the arithmetic pair L-factor is the reciprocal of `det(1 - X (A ⊗ B))` for the
Frobenius operators `A`, `B`. This module computes that polynomial from the Euler
polynomials of `A` and `B`, as needed to match the automorphic pair Euler polynomial
`∏ (1 - a_i b_j X)` of the Satake parameters (the outside-set matching in Henniart 2000,
Théorème 2.3). Internal linear algebra, no literature theorem beyond the standard identities.

## Results

- `coeff_polynomialTraceSeries_prod_linear`: the `k`-th coefficient (`k > 0`) of the trace
  series of `∏_(r ∈ s) (1 - r X)` is `∑_(r ∈ s) r^k` (published
  `polynomialTraceSeries_multiset_prod`, `coeff_polynomialTraceSeries_one_sub_C_mul_X`).
- `coeff_zero_polynomialTraceSeries`: the constant coefficient of every trace series is `0`.
- `coeff_zero_prod_linear`: `∏ (1 - r X)` has constant coefficient `1`.
- `coeff_polynomialTraceSeries_eulerPolynomial`: for an endomorphism `M` of a
  finite-dimensional complex space, the `k`-th coefficient (`k > 0`) of the trace series of
  `LocalFactor.eulerPolynomial M = det(1 - X M)` is `trace(M^k)`; via a finite basis, the
  Euler polynomial is the reversed characteristic polynomial of the matrix, and the published
  `matrixTraceGeneratingSeries` applies.
- `sum_map_product_pow`: `∑_((a,b) ∈ s × t) (ab)^k = (∑ a^k)(∑ b^k)`.
- `eulerPolynomial_tensorMap`: if `det(1 - X A) = ∏_(a ∈ s) (1 - a X)` and
  `det(1 - X B) = ∏_(b ∈ t) (1 - b X)`, then `det(1 - X (A ⊗ B)) = ∏_((a,b) ∈ s × t) (1 - ab X)`.
  Proof: both sides have constant coefficient `1`, and their trace series agree: the constant
  coefficients vanish, and for `k > 0` both coefficients are `trace(A^k) trace(B^k)`
  (`TensorProduct.map_pow`, `LinearMap.trace_tensorProduct'`). The published injectivity
  `polynomialTraceSeries_injective_normalized` concludes.
