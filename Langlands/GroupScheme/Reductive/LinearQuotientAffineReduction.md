# Actual affine linear homogeneous spaces from linear quotient affineness

This is an internal conditional reduction using published
Library constructions.

`exists_affine_linearQuotient_of_reductiveLinearQuotientAffine` assumes the
proposition `ReductiveLinearQuotientAffineStatement` at universe `u`.
For every algebraically closed field `k : Type u` and every actual connected
reductive group `G`, it supplies a finite-dimensional representation `ρ`
that is a closed subgroup embedding, together with an actual affine
homogeneous quotient of the general linear group by `ρ(G)`.

The implementation first uses `affineLinearEmbeddingStatement`; smoothness
of `G` gives its finite type hypothesis. The actual general linear group is
smooth by `GeneralLinear.smoothStatement` and affine by
`GeneralLinear.isAffineHom_groupScheme`. The published
`smoothSubgroupQuotientExistence` then produces a quotient scheme, its
projection, separatedness, local finite type, quasi-compactness, smooth
surjective quasi-compact projection, and exact right-coset fibers on all
relative scheme tests. These are packaged without alteration as a
`HomogeneousQuotient`. Finally the assumed affineness statement applies to
this very quotient.

This reduction introduces no external geometric theorem. Its imports and
proof use general linear groups, closed linear embeddings and smooth
subgroup quotients; it does not use a Borel or rank-one classification
result. Its hypothesis remains unproved here. In particular it proves
neither unconditional linear quotient affineness nor
`DynamicQuotientProperStatement`, and it does not construct the
extension argument needed for the properness application.
