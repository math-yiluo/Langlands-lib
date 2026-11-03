# Natural finite coordinates from actual Lie scalar extension

Author: Worker 1317.

For an affine group scheme locally of finite type over any field `k`,
`finiteCoordinatesOfBasis` constructs the published `Lie.FiniteCoordinates`
datum from a finite `k`-basis of its actual Lie kernel. `finiteCoordinates`
chooses the published finite-dimensional basis, with dimension equal to the
actual `k`-dimension. The coordinates are linear over each commutative test
algebra and natural under every algebra homomorphism. No smoothness,
reductivity, reducedness or characteristic assumption is introduced.

This is an internal construction derived from the actual scalar-extension
equivalence in `Lie.ScalarExtension` and the finite-dimensionality theorem
in `Lie.FiniteDimensional`. It supplies coordinates rather than assuming a
representation or determinant character.

First `lieKernelMapLinear_base` proves compatibility of successive coefficient
maps on vectors coming from the base field. The proof compares the actual
identity derivations and uses their published coefficient-change formula.
`kernelScalarExtension_naturality` then proves that the scalar-extension
equivalence commutes with arbitrary test-algebra homomorphisms. Tensor
induction reduces this to the pure-tensor formula, semilinearity, and the
successive-map result.

`kernelScalarExtension_adjoint` intertwines scalar extension with the actual
adjoint action of a base-field point and its image in the test algebra. It
uses tensor induction, linearity and the published adjoint naturality. This
compatibility statement only concerns points coming from the base field.

For a finite basis, scalar extension gives a basis of the tensor module.
Composing its coordinate equivalence with the inverse actual Lie
scalar-extension equivalence constructs `finiteCoordinatesOfBasis`. Tensor
induction proves coordinate naturality, using the basis coefficient formula
on pure tensors. Choosing `Module.finBasis` constructs the final
datum even when the dimension is zero.

This module does not yet identify actual adjoint weight spaces after a
base-field extension and does not prove opposite-root existence.
