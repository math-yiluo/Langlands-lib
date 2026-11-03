# Unipotence of affine group-scheme extensions

This internal derived unit proves closure under extensions using the Library's
finite coefficient-representation definition of `IsUnipotent`. The source
group scheme and its full scheme-theoretic kernel are affine over the field.
The quotient homomorphism is flat, scheme-surjective and quasi-compact. If
the kernel and quotient are unipotent, the source is unipotent.

For a representation of the source, kernel unipotence supplies a nonzero
kernel-fixed vector. A basis of the fixed subspace and a linear left inverse
of its inclusion give finite matrices `B` and `C` with `C B = 1`, fixed columns,
and `B C` acting identically on every fixed vector. The fixed subspace has
positive finite dimension.

The published normal-fixed-coordinate coefficient argument proves invariance
using affine models of the source and kernel. The published
`restrictCoordinates` construction gives an actual representation on this
space. Its restriction to the full kernel is trivial because every column of
`B` is fixed. `FpqcHomDescent.hom` descends it to an actual quotient
representation. Quotient unipotence supplies a nonzero fixed vector.
Intertwining transports that vector through the injective inclusion `B` to
a nonzero fixed vector of the original representation.

The reusable construction `MatrixRepresentation.quotientFixedCoordinates`
takes the coordinate matrices, their retraction equation, all-test stability,
and kernel-fixed columns. It returns an actual quotient representation.
`quotientFixedCoordinates_fac` identifies its pullback with the source's
restricted representation. This construction does not require affineness;
affineness of the source and kernel is used to establish stability in the
corollary `isUnipotent_of_kernel_of_quotient`.

The argument uses actual group-scheme homomorphisms and all scheme tests,
without pointwise surjectivity on rational points or a perfect-field
assumption. Its provenance is internal linear algebra and the published
fixed-coordinate, normality and fpqc homomorphism-descent constructions.
It does not construct a quotient or prove its affineness.
