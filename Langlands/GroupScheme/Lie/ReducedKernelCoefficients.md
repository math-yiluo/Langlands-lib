# Actual reduction-kernel coefficients over the quotient base

Let `R` be a commutative ring, `G` a smooth affine group scheme over `Spec R`,
and `I` an ideal with `I² = 0`. The canonical quotient-base coefficient module
`reducedKernelModule G I` is
`I.Cotangent ⊗[R] Additive (lieKernel G R)`, with its `R/I`-module structure
from the cotangent factor.

For every flat `R`-algebra `B`, `reducedKernelCoefficientEquiv` identifies the
actual additive kernel of `G(B) → G(B/IB)` with this coefficient module
extended to the actual base-changed algebra `(R/I) ⊗[R] B`. It combines
`FlatKernelCoefficients` with the inverse tensor equivalence of
`SquareZeroCotangentCoefficients`. The corresponding `reducedKernelPoint`
reconstructs an actual group point from a reduced-base coefficient.

The pure-tensor formula is the actual tangent evaluation formula: the tensor
`(1 ⊗ b) ⊗ (toCotangent(i) ⊗ X)` yields the Lie vector extended from the base
and evaluated in the ideal element with value `algebraMap R B i * b`.
Reconstruction carries sums to group products, recovers every actual kernel
point, and always reduces to the identity. Both reconstruction and the forward
coefficient equivalence commute with arbitrary morphisms between flat test
algebras. Naturality follows from the two constituent comparisons.

This internal construction supplies a quotient-base module and actual kernel
comparisons on flat affine tests. It retains the smooth affine target and
flat-test hypotheses. It does not construct a representation of a reduced
source group on this module, identify defects with cocycles, extend the
comparison to nonaffine targets, or prove infinitesimal lifting.
