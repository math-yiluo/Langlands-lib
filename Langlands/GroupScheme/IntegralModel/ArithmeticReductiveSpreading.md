# Arithmetic good reductive models from generic openness

This internal construction works in every universe `u` under an explicit
`GenericReductivitySpreadingStatement.{u}` premise. It chooses an actual good
arithmetic ambient model of each supplied connected reductive group over a
number field. The generic openness statement remains an input.

For `F : Type u` with its field and number-field structures and an actual
`G : GroupScheme (Spec (CommRingCat.of F))`, `ReductiveModelData F G` contains:

- A finite set `places` of finite places of the same `F`.
- An actual `IntegralModel R F G`, where
  `R = (places : Set (FinitePlace F)).integer F` is the actual S-integer
  subalgebra with its canonical inclusion into `F`.
- `IsReductive` of that integral model's group.
- For every `k : Type u`, every field structure on `k` and every `Algebra R k`,
  `IsConnectedReductive` of the pullback of that same integral group along
  `Spec.algebraMap R k`.

`reductiveModelData` takes the openness premise and `IsConnectedReductive G`
and constructs this data. No splitness, rank or choice of representation is
an input.

The implementation first uses `smoothIntegralModelData` to choose a smooth
affine model over a finite S-integer ring. The smoothness and affineness of
the original group are supplied by `IsConnectedReductive G`. Noetherianity
of the actual model ring follows from `adelicSIntegersNoetherian`.
Transport along the model's prescribed `genericIso` supplies connected
reductivity of its actual generic pullback, so the openness premise applies.

The resulting nonzero coefficient `r` is made a unit by
`numberFieldSIntegersUnitStage`. This chooses a larger finite set containing
the original set and uses the literal inclusion of the corresponding
S-integer rings. The new model is exactly `enlargeModel` of the original
model along this inclusion; its generic identification is the one fixed by
that construction.

`fieldReductive_baseChange_of_isUnit` gives connected reductivity for every
field-valued point of the enlarged ring. Its composition comparison identifies
these with the original fibres, where the image of `r` is nonzero because it
is a unit. Smoothness is preserved by `smooth_enlargeModel`.
`isReductive_of_fieldReductive` then establishes the exact integral
`IsReductive` predicate by applying the all-field assertion to the geometric
points used in that predicate.

`fieldReductive_enlargeModel` is the companion preservation theorem. Given
any actual arithmetic model with connected reductivity at all its field-valued
points, it proves the same assertion for its canonical enlargement along
any supplied containment of finite place sets. It applies the same
composition comparison with the coefficient `1`; no generic openness premise
is needed for this preservation step.

The provenance is internal: these declarations combine the imported smooth
arithmetic descent, arithmetic unit-stage construction and exact fibre
comparisons. They do not supply a proof of generic reductivity openness,
a parabolic model or the full simultaneous spreading existence proposition.
