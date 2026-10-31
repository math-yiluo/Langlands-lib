# Homogeneous components of symmetric tensor modules

This internal construction tensors the canonical projections of
`SymmetricAlgebraHomogeneous` with the identity of an arbitrary module `V`.
It works over a commutative ring and allows independent universes for the ring
and both modules. It uses the actual tensor product of the genuine symmetric
algebra with `V`.

`tensorComponent` projects the symmetric factor onto degree `d`.
`IsHomogeneousTensor` says that this projection fixes the tensor. Repeated
projections satisfy the Kronecker formula, and every tensor has a finite
canonical decomposition with all higher projections zero. Multiplication by a
symmetric coefficient satisfies the antidiagonal convolution formula. On a
tensor homogeneous of degree `e`, the degree `d` projection selects the
coefficient component of degree `d-e` when `e ≤ d`, and is zero otherwise.

Naturality holds for a symmetric-algebra map induced by any linear map on its
generating module and any linear map on the second tensor factor. Thus an
equivariant diagonal action induced from these maps commutes with the
projections. No compact group, finiteness, or characteristic assumption is used.

The proofs reduce projection and naturality formulas to pure tensors.
Convolution follows from the coefficient product formula. The finite
decomposition begins with the auxiliary polynomial's finite degree on a pure
tensor and combines bounds by taking maxima under addition. The selected-degree
formula retains the unique nonzero term of the antidiagonal sum.

This is a derived prerequisite for homogeneous covariant generators and degree
control in filtered central generation. It proves neither finite generation of
covariants nor an automorphic growth statement.
