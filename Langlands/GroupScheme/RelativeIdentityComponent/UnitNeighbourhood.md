# An open unit neighbourhood inside the relative identity set

This internal construction forms the union, over all base points, of the
component images in the affine unit neighbourhoods. Each image lies in the
published underlying relative identity set by the unit-section comparison.
The chosen base point lifts to its affine base neighbourhood, and the
restricted section maps that lift to the ambient unit point. Thus the union
contains every point of the actual unit section.

Assuming the generic flat finite-presentation section-component openness
proposition, each component union is open in its affine total neighbourhood.
Its image is open because the neighbourhood inclusion is an open immersion.
The union is therefore an open subset of the ambient group. The construction
uses arbitrary bases and smooth group schemes, with no global finiteness
hypothesis.

Multiplication of a smooth group scheme is smooth: the published left shear
of the square, applied to the identity family, identifies multiplication
with the second projection after an isomorphism. The projection is a base
change of the smooth structure map. Flatness and local finite presentation
then make multiplication an open map.

`unitOpen`, `unitOver` and `unitInclusion` give the actual open subscheme and
its inclusion over the base. Its range is exactly the union just constructed.
`unitProduct` is multiplication on the actual fibre product of two copies
of this open subscheme. The tensor of the inclusions is an open immersion
by base-change and composition stability. Its composite with multiplication
is smooth, so its image is open.

These statements are derived from the existing affine neighbourhoods, their
section equations, the published shear and the standard smoothness and
openness results. The generic openness theorem is an explicit premise. This
module does not yet identify the product image with the relative identity
set and does not prove the unconditional smooth structure statement.
