# The adjoint representation on quotient-base ideal coefficients

Let `R` be a commutative ring and `G` a smooth affine group scheme over
`Spec R`. For any ideal `I`, the canonical quotient-base module
`Lie.SquareZero.reducedKernelModule G I` is
`I.Cotangent ⊗[R] Additive (lieKernel G R)`. Its scalar ring is `R/I` through
the cotangent factor. The constructions in this file do not require `I² = 0`.

`reducedAdjointModuleRepresentation` gives an actual natural representation
of the group scheme `G` base changed to `Spec(R/I)` on this module. It starts
with the actual adjoint representation of `G`, extends its coefficients and
group to `R/I` by `Cohomology.BaseChange`, tensors with the trivial action on
`I.Cotangent`, and transports along `reducedAdjointCoefficientEquiv`.
This last equivalence commutes the tensor factors and cancels scalar extension:

`((R/I) ⊗[R] Lie(G/R)) ⊗[R/I] I.Cotangent ≃ I.Cotangent ⊗[R] Lie(G/R)`.

Its pure-tensor formula sends `(c ⊗ X) ⊗ i` to `(c • i) ⊗ X`, and its
inverse sends `i ⊗ X` to `(1 ⊗ X) ⊗ i`. The equivalence and these formulas
need only an affine target; smoothness is used for the existing actual
adjoint module representation.

`reducedHomomorphismCoefficients` restricts this natural representation along
any actual homomorphism from a group scheme over `Spec(R/I)` into the reduced
`G`. No conditions are imposed on this source group.

This internal construction supplies the actual reduced group action on the
canonical module. It does not prove that this action corresponds, through
`ReducedKernelCoefficients`, to conjugation on arbitrary actual square-zero
kernel points. That compatibility, the identification of defects with regular
cocycles, and the nonaffine target case remain separate obligations.
