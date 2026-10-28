# Scalar covariance for actual two-block induction

This module proves the closed
`Langlands.Whittaker.TwoBlockInducingWhittakerCovarianceStatement`, an internal
prerequisite for the JPSS extension construction.

`pairFunctional_blockTensor_unipotent` first proves equality of linear maps out
of the actual finite tensor product. On pure tensors, the block action is the
tensor of the two actions and `pairFunctional` is the product of their values.
The two given Whittaker identities and commutativity of complex multiplication
finish the pure tensor calculation. Tensor extensionality then gives the result
on arbitrary tensors.

The main theorem uses the actual block diagonal Levi section. Each unipotent
block has determinant one, hence normalized determinant norm one. The two-block
modulus formula therefore gives modulus one; its positive square root is also
one. `normalizedProductInduced_covariant` reduces evaluation at the left block
diagonal translate to the tensor action on the original evaluation. Applying the
previous tensor identity proves the exact scalar formula. This proves no
integrability or extension assertion.
