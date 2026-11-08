# Reductivity of the actual special linear group

This internal support construction proves triviality of the unipotent radical
and reductivity for the actual determinant-one group scheme
`SpecialLinear.groupScheme`. The field and base-ring universe is arbitrary, and
the matrix index is any finite type in `Type` with decidable equality.
Triviality of the radical includes the empty index. The smoothness,
connectedness and reductivity conclusions take a chosen pivot in the index,
as required by the determinant retraction in `SpecialLinearGeometry`.
There is no characteristic restriction.

`eq_top_of_forall_SL_mulVec_mem` proves that a nonzero subspace stable under
all determinant-one matrices is the whole standard vector space. Given a
nonzero coordinate `v p`, subtracting a vector from its image under the
transvection `1 + E(q,p)` gives `v p` times the `q`th basis vector for
`q ≠ p`. Scaling gives those basis vectors; one more transvection gives the
`p`th basis vector. If the index has only one element, scaling the original
vector supplies that basis vector directly. Finite sums then supply every
vector. All transvections used have determinant one.

`constantMatrixPoint` transports a special-linear matrix over the base field
to every relative test scheme by its actual structural coefficient map.
`mulVec_mem_fixedSubmodule` proves that the fixed space of a normal subgroup
is stable under these matrices. Normality here is in the special linear group
itself. Conjugating a test point by the constant matrix stays in the subgroup;
the representation obtained by composing with the actual inclusion into
`GL` converts this conjugation identity into invariance of the transformed
vector. The argument quantifies over every test scheme and point.

`SpecialLinear.hasTrivialUnipotentRadical` applies the definition of unipotence
to that standard representation to obtain a nonzero fixed vector. The preceding
stability and subspace argument make the entire vector space fixed. Testing
each basis vector over every relative test scheme shows that every matrix in
the subgroup image is the identity. The actual special-linear point
equivalence then identifies the subgroup functor image with the trivial
subgroup. For an empty index, there are no matrix entries to check. This proves
the exact existing `HasTrivialUnipotentRadical` property; it does not assume
that the subgroup is normal in `GL`.

`SpecialLinear.isPseudoReductive` combines this result with smoothness,
affineness and field connectedness of the actual coordinate model.
`SpecialLinear.isConnectedReductive` uses `baseChangeModelIso` to identify its
base change to the algebraic closure with the same special-linear model over
that closure, where the radical result applies again. Finally,
`SpecialLinear.isReductive` uses the same comparison for every geometric
fiber over an arbitrary commutative base ring.

The provenance is internal. The fixed-subspace route follows the existing
general-linear argument in `Reductive.GeneralLinear`, using only actual
special-linear transvections and normality in the special linear group.
The coordinate geometry and the base-change isomorphism are imported established
constructions. This module does not supply classification of local rank-one
groups, rational Bruhat decomposition, or the unrestricted local Kneser–Tits
theorem.
