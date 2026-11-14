# Bounded adjoint images of dense bounded subgroup normalizers

The proved definition `denseBoundedNormalizerAdjoint` has exactly the type
`DenseBoundedNormalizerAdjointStatement.{u}`. For a connected reductive group
over a nonarchimedean local field in arbitrary universe `u`, a supplied actual
adjoint quotient, and an algebraically bounded Zariski-dense rational subgroup,
the actual normalizer has algebraically bounded image in that quotient.

A connected reductive group is smooth and affine of finite type, and smoothness
over the field makes its underlying scheme reduced. Choose a closed faithful
matrix representation. Density of the rational subgroup constructs the actual
conjugation representation on the span of the subgroup's matrix and inverse
matrix values. Its full scheme kernel is the center.

The normalizer preserves the retracted subgroup coordinate generators. They
span the restricted coordinate space and are bounded because the subgroup is
algebraically bounded and closed under inversion. The proved
`ConjugationSubrepresentation.isAlgebraicallyBounded_normalizer_image`
therefore bounds the actual normalizer image in this representation. The
general linear target is affine and smooth, hence locally of finite type.
The closed adjoint descent helper
`isAlgebraicallyBounded_adjoint_image_of_kernel_eq_center` transfers that bound
to the supplied actual adjoint quotient. Its construction uses the full scheme
kernel, including all scheme tests; it requires no lifting of rational points.

The proof is an internal composition of the closed linear embedding theorem,
smooth reducedness, the conjugation-span construction and full kernel theorem,
the bounded spanning-family action argument, and closed-immersion reflection
of algebraic boundedness. All these inputs are supplied by proved declarations.
This is a derived intermediate result for KP Proposition 2.2.16. Passing from
an open subgroup to a dense family and controlling the central directions by
the rational common norm kernel are handled in separate modules.
