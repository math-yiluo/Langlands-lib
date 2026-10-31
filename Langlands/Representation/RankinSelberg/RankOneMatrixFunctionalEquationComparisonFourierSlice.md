# Fourier inversion on complementary affine coordinate slices

Author: Worker 623.

This internally derived helper proves partial Fourier inversion with the actual
supplied scalar Haar measure. It works over a locally compact Hausdorff totally
disconnected topological field with its Borel measurable space. The supplied
scalar measure is sigma finite and self dual for the supplied continuous
nontrivial unitary additive character. Every finite dimension, including zero,
and every subset of the coordinates is allowed.

`coordinateSliceMeasure ν S c` is the product measure whose coordinates in
`S` carry `ν` and whose remaining coordinates carry the Dirac measure at the
corresponding entry of `c`. Thus it integrates on the actual affine slice,
without choosing a new normalization. `coordinateMask S a` retains the
coordinates of `a` in `S` and sets the others to zero.

For a Schwartz function `Φ`, write `Φhat` for its actual plus row Fourier
integral. `coordinateSlice_fourier_duality` proves absolute convergence and
the equality

```text
∫ Φhat(y) ψ(-sum_(i in S) a_i y_i) d(slice(S,b))(y)
  = ∫ Φ(x) ψ(sum_(i outside S) b_i x_i) d(slice(S-complement,a))(x).
```

The transformed free coordinates are fixed at `a` on the original side.
The transformed fixed coordinates `b` become the original-side plus phase.
There is no volume factor, since scalar self duality is used with the same
measure in each free coordinate.

The proof uses the published finite tensor decomposition of Schwartz
functions. For one tensor, finite product integration reduces the claim to
scalar Fourier inversion in each coordinate of `S` and to the defining
scalar Fourier integral in each other coordinate. Tensor integrability is
proved separately from scalar integrability and Dirac integrability.
Finite linear combinations give both absolute convergence and the equality
for every Schwartz function.

The provenance is internal: this is a finite product consequence of the
published `IsSelfDual`, `rowTensorDecomposition` and row Fourier definitions
and Mathlib's product and Dirac integration theorems. It supplies the
coordinate Fourier step used in a future affine-matrix specialization.
It asserts no Whittaker integral comparison, matrix zeta convergence,
same-vector block extraction or gamma functional equation.
