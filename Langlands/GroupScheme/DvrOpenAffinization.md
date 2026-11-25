# Open affinization maps over a DVR

Let `f : G → H` be an actual open-immersion homomorphism over a DVR. Suppose
`G` is smooth and quasi-compact over the DVR, `H` is affine, and the actual
map on global functions induced by `f` is bijective. `specialFiberIso`
constructs the actual isomorphism on quotient-residue-field fibres whose
forward map is precisely the original base-changed map.

If the actual generic-fibre map is also an isomorphism, `isoOfGeneric`
constructs an actual isomorphism of the total schemes with forward map the
original `f`. Every point of `Spec R` is generic or closed. On either fibre,
surjectivity of the corresponding base-changed map lifts every target point
to a source point, using the exact range formula for the pullback projection.
Thus the total open immersion is surjective, hence an isomorphism.

## Implemented proof and provenance

This is an internal replacement for the field-affineness and Hopf-algebra
steps in the usual smooth-DVR affinization proof. The actual special-fibre
map is still an open-immersion group homomorphism. Its image is closed by
`FieldOpenSubgroup.isClosed_range`, which requires no finite type of the
ambient group. The source fibre is quasi-compact and the target fibre is
affine. `DvrSpecialFiberSectionEmbedding.appTop_injective` therefore makes
that image dense. Closedness and density give surjectivity, so the actual
special-fibre map is an isomorphism.

No connectedness, commutativity or henselianity hypothesis is used. The
affine target and its special fibre are not assumed smooth, reduced or of
finite type. This construction does not prove that the original map
is an open immersion or construct any affinization group law.
