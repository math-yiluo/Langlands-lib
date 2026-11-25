# Linear lift into a tensor of functions

Product evaluation is injective when the factor evaluations are
injective. For a linear family of functions taking values in its range,
restrict the map to that range and apply the inverse of product
evaluation. The resulting tensors depend linearly on the input.

Finite-dimensional slices in each coordinate ensure that every value
admits such a tensor. The slice spaces can vary with the input, since
uniqueness takes place in the common ambient coefficient tensor.
This internal construction supplies the linear coefficient map for
the constant-term sections in the proof of `CuspidalSupportExistenceStatement`
(`Langlands.Global.Factors.CuspidalSupportExistenceProof`).
