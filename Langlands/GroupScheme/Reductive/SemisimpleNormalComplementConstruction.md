# Normal complements from almost-simple generation

Worker 1454, using Worker 1466's full-centralizer and commuting-multiplication
constructions.

`semisimpleNormalComplementOfAlmostSimpleGeneration` chooses a
`CommutingNormalComplement j` for a smooth connected closed normal subgroup
of a semisimple group over an algebraically closed field. It works in every
universe and characteristic, conditional on the separate proposition
`SemisimpleAlmostSimpleGenerationStatement`. Its chosen complement is the full
centralizer supplied by `closedNormalCentralizer`. This group is closed and
normal and commutes with the given subgroup on every test scheme. It need
not be smooth.

The closed subgroups are affine and locally of finite type because the
semisimple ambient group is smooth and affine. Their product has the same
properties. All-test commutation gives the actual group homomorphism
`commutingSubgroupMultiplicationHom`, whose underlying scheme morphism is
exactly `subgroupMultiplication`. Its range contains each factor, by pairing
a point in that factor with the identity in the other.

For any closed normal almost-simple subgroup, the previously proved
`IsAlmostSimple.range_le_or_commute_of_normal` gives two cases. The subgroup
either lies in the given subgroup or commutes with it on every test.
The full-centralizer comparison puts it in the centralizer in the latter
case. Its range therefore lies in the range of multiplication in both cases.
`flat_surjective_of_contains_almostSimple_factors` now applies the generation
premise to the schematic image and proves flatness and surjectivity of the
actual multiplication morphism.

`semisimpleNormalComplement_of_almostSimpleGeneration` forgets the chosen data
to obtain precisely `SemisimpleNormalComplementStatement`, still conditional
on generation. This internal assembly does not prove the generation premise
and is not an unconditional proof of the complement target.
