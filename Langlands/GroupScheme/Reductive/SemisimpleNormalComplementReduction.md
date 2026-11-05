# Normal complements from almost-simple generation

Author: Worker 1454.

`CommutingNormalComplement j` bundles an actual group scheme, its closed
inclusion into the ambient group, normality of its full range, commutation with
the given subgroup on every test scheme, and flatness and surjectivity of
the actual `subgroupMultiplication` morphism. This data type is defined over
an arbitrary base scheme and universe. It imposes no smoothness on the
complement. `CommutingNormalComplement.exists` forgets the choice to the
corresponding existence assertion.

The companion theorem reduces flatness and surjectivity to
`SemisimpleAlmostSimpleGenerationStatement`. The module gives no
unconditional proof of that structural statement or of the complement target,
and it does not construct a complement.

`flat_surjective_of_contains_almostSimple_factors` treats a homomorphism from
an affine group locally of finite type to a semisimple group over an
algebraically closed field, at arbitrary universe and in every characteristic.
If its full range contains every closed normal almost-simple subgroup, the
independent generation statement forces its affine schematic image to be the
entire target. The schematic-image inclusion is a monomorphism and admits a
section by applying fullness to the identity of the target, hence is an
isomorphism. The original homomorphism is therefore schematically dominant.
The published `DominantHom.flat_surjective` supplies flatness and surjectivity
of its actual underlying scheme morphism. No smoothness or connectedness of
the source is required.

This is internal infrastructure for the complement target. The data fields
record precisely its requested witnesses. The companion proof assembles the
published affine schematic image and dominant-homomorphism constructions with
the separately stated generation prerequisite; it assumes no additional
decomposition theorem.
