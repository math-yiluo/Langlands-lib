# A fixed reflection normalizer and its translated root cell

This internal supporting construction combines the Library relative root system,
rank-one opposite-factor existence, reflection uniqueness, and exact normalizer
lifting. It does not assert the final unramified facet root datum.

For an affine field group with a monic split torus map, supplied actual relative
root system and rank-one factorization, any fixed rational normalizer representing
the reflection in an actual root `a` has the following property. Every
nonidentity rational point `x` of the intrinsic root subgroup `U_a` admits
`x = y z n w`, with `y,w` in `U_-a` and `z` in the actual torus centralizer.
Equivalently, `x n⁻¹` admits an opposite-centralizer-positive factorization.

The proof obtains an actual opposite factor pair for `x`. Its normalizing
product represents the same reflection as the fixed `n`, by uniqueness in the
actual relative root system. Their quotient therefore centralizes the torus.
Inverting the two opposite factors gives the asserted factorization. Conjugation
by `n`, which negates `a`, turns its final opposite factor into a positive
factor for the ordinary cell.

For a connected reductive group and a maximal split torus, the published
`relativeRootSystem` and `rootRankOneFactorization` supply the structural
hypotheses over every field. `reflectionNormalizer` chooses a rational
representative of the reflection before the variable point `x` is supplied.
`reflectionNormalizer_translatedCell` retains this one representative for every
nonidentity point of the root group.

Over a perfect field, let `q : G → Q` be the actual fppf quotient of an affine
group by a represented smooth connected closed unipotent subgroup, and let the
image of a torus map `i` be maximal split in a connected reductive `Q`.
`reflectionNormalizerLift` returns an actual source point and an actual
automorphism of the same torus. It preserves the exact chosen quotient
normalizer, normalizes the source torus map through this automorphism, and
negates `a` on its integral character lattice.
`reflectionNormalizerLift_translatedCell` gives the preceding cell translated by
the image of that same source point. The implementation applies the independently
developed exact perfect-field unipotent-kernel normalizer lift.

All declarations retain arbitrary universe `u`. These interfaces require `a` to
be an actual root of the reductive target. They do not assert that every source
root survives in the target, compare a disappearing character with a surviving
higher multiple, identify dynamic root groups, lift cell factors to integral
sections, or prove strict-depth quotient vanishing.
