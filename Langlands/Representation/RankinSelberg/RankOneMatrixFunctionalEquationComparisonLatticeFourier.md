# Rectangular Fourier integrals of affine lattice boxes

Author: Worker 623.

This internally derived helper constructs the actual Schwartz–Bruhat
characteristic test of an entrywise affine lattice box over any supplied
topological data of a p-adic field. Every entry has its own integer level and
centre. Both dimensions may be zero.

For the supplied character `ψ`, additive Haar measure `μ`, levels `m`, centre
`A` and Fourier argument `Y`, it proves convergence and the exact plus Fourier
formula

```text
Fourier(1_(A + L_m))(Y)
  = (product_i product_j μ(L_(m_ij)).toReal)
      * ψ(sum_i sum_j A_ij Y_ij)
      * 1_(L_(conductor(ψ)-m))(Y).
```

The volumes are complex casts of the real masses of the actual scalar
lattices. No self-duality or measure normalization is required for this
formula. The supplied unitary additive character is continuous and nontrivial
by its definition. The dual support depends on its actual conductor.

The implementation proves compactness of each affine lattice coset by
translation, then compactness of the box by two finite products. Openness
follows by continuous subtraction and finite products. The characteristic
function is therefore an actual Schwartz–Bruhat test. Two applications of
finite-product Bochner integration factor its Fourier integral into scalar
ones. Actual integrability is proved separately from the scalar convergence
theorem using two finite products of integrable functions. The published
`padicLatticeFourier` theorem evaluates each scalar factor, and the additive
character law recombines the phases.

Provenance is internal: the construction and computation use the published
`PadicLatticeFourierProof`, actual rectangular pairing and nested product
measure, `Hecke.TestFunction.characteristic`, and Mathlib's finite-product
integration. This helper asserts no Whittaker integral comparison, paired
block extraction, convergence of matrix zeta integrals or gamma functional
equation.
