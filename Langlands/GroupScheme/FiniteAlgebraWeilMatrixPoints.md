# Finite matrix algebra units in the Weil tensor convention

This internal comparison reorders the tensor factors in the published actual
point model of the finite matrix algebra unit group. The base K and coefficient
field L are arbitrary fields with an algebra structure. A finite K-basis of the matrix algebra is supplied explicitly. Every actual test
scheme is allowed.

The multiplicative equivalence `tensorMatrixEquiv` composes the published
`MatrixPoints.tensorMatrixEquiv` with the tensor swap from sections tensor L to
L tensor sections. This is the convention of
`SpecialLinear.WeilRoot.tensorAlgebra`. Tensor induction proves that this
comparison respects every test pullback.

For any all-test family of matrix group homomorphisms, `unitPoints` reinterprets
the matrices as actual points of the finite algebra unit group. Its naturality
follows from the supplied entrywise naturality and the comparison above.
`hom` is the resulting actual group-scheme morphism, constructed by the
published group-valued Yoneda API. `tensorMatrixEquiv_hom` verifies that its
point action is exactly the supplied matrix family. If that family is injective
on every test scheme, cancellation on all test points proves that the morphism
is a monomorphism, also on underlying schemes.

These are intrinsic tensor and Yoneda comparisons, derived from the published
finite-algebra and Weil point models. No Hermitian form, determinant condition,
quadratic extension, separability or restriction on characteristic is assumed.
