# Actual Whittaker model comparison at real and complex places

`ArchimedeanPlaceWhittakerModelsStatement.{u}` conjoins
`RealPlaceUniformWhittakerModelStatement.{u}` and
`ComplexPlaceWhittakerModelStatement.{u}`. Under each comparison's hypotheses,
including the specified local parameter of the cuspidal realization, actual
Whittaker restrictions belong to the corresponding local model. The original
additive character and its inverse use the local scales \(a\) and \(-a\),
respectively.

`archimedeanPlaceWhittakerModels` uses `realPlaceUniformWhittakerModel` for
the real conjunct. For the complex conjunct, `complexPlaceWhittakerAnalytic`
supplies smoothness, growth, and compatibility with the Lie algebra action.
`complexPlaceWhittakerIntertwinerReduction` turns these properties into the
intertwiner premise for `complexPlaceWhittakerModelReduction`, which gives
membership in the complex model.

This internal Library proposition provides a single import for the two
comparisons. The complex implementations use private names for the local
instances whose names collide with their real counterparts.
