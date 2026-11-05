# The actual fppf image theorem from Hopf-subalgebra faithful flatness

The internal theorem `affineHomImage_of_hopfSubalgebraFaithfullyFlat` proves
the exact proposition `AffineHomImageStatement` from the explicit
Hopf-subalgebra faithful-flatness input over every field at the same arbitrary
universe. This reduction has no smoothness, reducedness, connectedness or
perfectness premise on the actual groups or their base field.

The intermediate group is the existing actual schematic image
`AffineHomImage.image f`. Its original projection and closed inclusion give
the factorization. Its structure morphism is affine and locally of finite
type, by the corresponding published instances.

The projection is schematically dominant. The conditional coordinate adapter
therefore proves that the projection is flat and scheme-surjective. Its
local finite type property follows from the source structure morphism.
The image is locally Noetherian because it is locally of finite type over a
field, so the projection is locally of finite presentation.

Finally, `AffineHomImage.kernel_range_projection` identifies the full kernel
range on every test scheme with that of `f`. These four properties give
`RelativeRoot.IsFppfQuotient` in the exact target. This does not assert
surjectivity of the map on points of each fixed original test scheme.

This is a derived reduction using the published schematic image, coordinate,
and kernel results. The remaining explicit algebraic input is supplied
separately; this file alone does not prove its unconditional validity.
