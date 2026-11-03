# Scalar extension of the actual affine Lie kernel

Author: Worker 1317.

This internal construction derives scalar extension of the actual dual-number
identity kernel from the published affine coordinate and finite derivation
coefficient comparisons. For an affine group scheme `G` locally of finite type
over an arbitrary field `k` and any commutative `k`-algebra `A`, it constructs

`kernelScalarExtension G A :
  A ⊗[k] Additive (lieKernel G k) ≃ₗ[A] Additive (lieKernel G A)`.

It requires no smoothness, reductivity, reducedness or nontriviality of `A`.
Both the base field and the test algebra are in the original universe.

The construction first works with derivations of the chosen affine coordinate
algebra at the identity. `originBaseLinear` postcomposes scalar-valued
derivations with `k → A`; `identityDerivationTensorMap` extends this map by
`A`-linearity. On pure tensors it sends `a ⊗ d` to the derivation
`c ↦ a * algebraMap k A (d c)`.

To prove bijectivity, choose a `k`-basis of `A`. Its coefficient equivalence
respects the coordinate-algebra action through the identity augmentation.
The published `derivationFinsuppLinearEquiv` therefore expresses derivations
with values in `A` as a finitely supported family of scalar-valued derivations.
Finite type of the coordinate algebra supplies uniform finite support.
The resulting coefficient map intertwines the tensor map with Mathlib's basis
coefficient equivalence for the left tensor factor. This proves both
injectivity and surjectivity. The proof uses a basis to establish bijectivity;
the tensor map itself is the natural one and contains no basis choice.

`kernelScalarExtension` transports that equivalence through the published
`kernelDerivationLinearEquiv`. Its pure-tensor formula recovers the actual
coefficient-change map on Lie kernels followed by scalar multiplication.
This module alone does not identify adjoint weight spaces after changing the
base field or prove opposite-root existence.
