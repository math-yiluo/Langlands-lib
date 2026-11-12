# Smooth lifting over Henselian local rings

This is a derived internal prerequisite for the integral-point step of Conrad's
Theorem 5.9. It uses the published affine étale chart lifts for field points and
Henselian integral points, smoothness on every compatible étale chart square,
and smooth scheme point lifting over a Henselian local ring.

For a smooth morphism of algebraic spaces over a Henselian local ring, a point
of the source over any surjective field quotient lying above the reduction of
a supplied integral target point lifts to an integral source point with exactly
that target and reduction. No separatedness, finite type, surjectivity of the
space morphism, or connectedness of its fibres is assumed.

`exists_lift_over_local_base` proves this over the local coefficient ring.
`exists_lift` preserves an arbitrary original coefficient base: it base changes
the two spaces and their smooth map to the local ring and transports both
equations by the published point equivalences, natural in space morphisms and
coefficient maps. `pointLift` chooses an actual lift carrying both equations,
and `surjective_of_residue` deduces integral-point surjectivity from
residue-point surjectivity.

The proof lifts the target integral point and the source field point to actual
étale scheme charts. Their fibre product over the target space is a scheme.
Its projection to the source chart is étale, so its map to the target chart is
smooth by the published chart comparison theorem. The compatible field points
give a point of this fibre product. Smooth scheme lifting gives an integral
point with its specified reduction; composition with the chart map gives the
required algebraic-space point and both exact equations.

This result does not construct residue-field points, establish a Lang–Weil
estimate, descend arithmetic models or prove adelic openness.
