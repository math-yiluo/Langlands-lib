# Convolution and tensor products of linear maps

For a commutative bialgebra `H`, its comultiplication is the convolution product of the two canonical algebra maps into `H ⊗ H`. Applying the convolution formula reduces the assertion to the fact that the two tensor inclusions induce the identity on the tensor product.

`WithConv.mulTensor` combines linear maps on two modules into a linear map on their tensor product. On a pure tensor it multiplies the two output values, in the given order. For coalgebra structures and a commutative target, this operation preserves products of pairs under convolution. The proof uses Mathlib's compatibility of tensor maps with convolution and postcomposes with multiplication in the target.

For an algebra map `g : A →ₐ[R] S`, the composite of `g` with the multiplication of `A` is `mulTensor g g` (`AlgHom.toConv_toLinearMap_comp_mul'`), which restates that `g` is multiplicative. The lemmas on zero, sums and scalar multiples in each factor are checked on pure tensors.
