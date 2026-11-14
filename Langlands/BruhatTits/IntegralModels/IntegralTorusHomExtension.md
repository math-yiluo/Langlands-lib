# Extending generic torus maps compatibly with integral inclusions

Over a domain R with fraction field K, these constructions retain the actual
supplied integral tori, their prescribed generic identifications, and ambient
model inclusions. The universe is arbitrary and no characteristic restriction
is imposed.

For `IntegralTorusData A` whose integral torus is split,
`A.splitTorusModel` packages that very torus as an affine flat finite type
model of its prescribed generic torus. Affineness and smoothness follow from
splitting. `A.splitTorusModelInclusion` packages its original inclusion into
the neutral model as a morphism of models with the same generic square.

For `IntegralSplitTorusData A` in a model N, another integral split torus T,
and a specified actual generic map f from T_K to A's prescribed generic torus,
`A.fieldHomExtension` chooses a homomorphism T to A.torus. Its generic fibre,
followed by A's supplied generic identification, is exactly f. This is the
general field-fibre extension from `Torus.FieldHomExtension`, applied after
composing f with the inverse generic identification.

If an actual integral map j from T to N has generic fibre f followed by the
prescribed generic inclusion, `fieldHomExtension_comp_inclusion` proves the
literal integral equality between j and the extended torus map followed by
A.inclusion. The proof compares the two generic maps using the two generic
squares, then applies generic-fibre injectivity: T is flat because it is smooth,
and the affine model N is separated.

These are internal constructions and consequences of the existing split-torus
and integral-model APIs. They assert neither existence of recovered apartment
models nor coefficient-stable chambers, and do not identify any entire neutral
integral-point subgroup with a zero fixer.
