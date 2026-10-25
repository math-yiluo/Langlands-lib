# Complex unitary scalar comparison and inclusion

This internal construction uses the actual rational unitary group and the
Harris complex unitary splitting. The direct-versus-iterated comparison
`complexDirectUnitaryGroupSchemeIso` applies the existing group-scheme
pullback composition isomorphism and the equality of the scalar maps for
Q to R to C and Q to C. Composing its inverse with the existing unitary
splitting gives `directComplexUnitaryGroupSchemeIso`, an isomorphism from
the actual direct complex pullback to the finite product of general
linear groups. Only the splitting requires the supplied signature charts.

`complexUnitaryInclusion` is the successive pullback of the original
rational unitary inclusion. The model comparison square is proved by
applying the complex base-change functor to the existing real
scalar-extension inclusion square. On every complex test scheme,
`complexUnitaryInclusion_points` proves that inclusion preserves the
unitary matrices and adds precisely multiplier one in the similitude
coordinates. It uses the actual inclusion square and the published
all-test-scheme formula for base-changed unitary inclusion, followed by
the scalar unitary splitting formula.

These are compatibility constructions for existing schemes. They do
not establish chart existence, smoothness, reductivity, canonical
models or Shimura-level representability. The provenance is internal:
pullback composition, the original scalar-extension square and the
actual unitary/similitude point equivalences supply every ingredient.
All new code is by Worker 57.
