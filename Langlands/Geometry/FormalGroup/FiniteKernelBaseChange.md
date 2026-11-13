# Tensor base change of actual finite kernel representations

For an O-algebra map φ : R → S, this module constructs the tensor
base change of an existing finite kernel representation. The rings
R, S and all test and kernel algebras lie in the same universe.
No flatness of φ is assumed.

`coefficientTensorAlgebra φ C` is the commutative S-algebra
S ⊗[R] C, with the R-algebra structure on S induced by φ.
`coefficientTensorHomEquiv` is its universal property: maps from this
tensor algebra to an S-algebra A are in bijection with maps from C
to A viewed as an R-algebra along R → S → A. It is implemented using
Mathlib's `AlgHom.liftEquiv`. Restriction evaluates a tensor-algebra
map on 1 ⊗ c, and the inverse extends an R-algebra map by S-linearity.
Postcomposition commutes with this restriction.

For `K : Hom.FiniteKernelModel f`, `K.baseChange φ` has coordinate
algebra S ⊗[R] K.coordinateAlgebra. Its module is finite and projective
over S by extension of scalars. To prove that it corepresents the
actual point kernel of f_S, the construction composes the tensor
universal property with K's natural corepresentation of the original
kernel on restricted test algebras, then applies the actual kernel
comparison of `CoefficientPoints`. Naturality follows from
postcomposition compatibility and K's corepresentation naturality.
Thus the new finite algebra represents precisely the evaluated
base-changed kernel.

`rank_baseChange` proves that the stalk rank at a prime p of S equals
the original stalk rank at its inverse-image prime in R. This is
Mathlib's finite-module rank-under-base-change theorem applied to the
constructed tensor algebra. Consequently
`Hom.HasFiniteLocallyFreeKernel.map` and `Hom.HasKernelRank.map`
preserve the finite-kernel and constant-rank conditions under
arbitrary coefficient extension.

This is internal infrastructure derived from `FiniteKernel`,
`CoefficientPoints`, the universal property of a tensor product and
finite projective extension of scalars. It does not establish affine
fppf lifting after base change, isogeny or scalar-divisibility
preservation, height additivity, rational heights, local gluing,
or moduli representability.
