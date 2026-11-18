# Smoothness of the actual odd norm-one group

The actual reduced-norm-one isometry group of the standard odd quadratic
form `z² + sum x_i y_i` is smooth over every ground field. This includes
imperfect fields of characteristic two, where the full isometry scheme
is not assumed smooth.

The proof uses `TangentChart`: the actual product of the smooth even
orthogonal group and the signed additive groups maps to the odd group by
ordered multiplication. It preserves the identity, and every actual odd
identity tangent point has a normalized source lift. The general theorem
`smooth_of_lieKernel_surjective_chart` then supplies smoothness, using
rational tangent surjectivity, smooth source descent onto a nonempty open,
and the published field-group smooth-open-chart criterion.

This is an internal application of those previously proved constructions.
No new classification, reductivity, connectedness, or central-isogeny
assertion is made here. The index type is finite in `Type`; the field
universe is arbitrary.

`smoothSourceChart` packages the actual source group, ordered chart, source
smoothness, identity equation and tangent lift property as data. The
smoothness instance is the same application of the general criterion.
