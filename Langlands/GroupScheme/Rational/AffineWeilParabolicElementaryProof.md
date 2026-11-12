# Parabolic radical generation under affine Weil restriction: proof

Author: Worker 111.

`Langlands.GroupScheme.affineWeilParabolicElementarySubgroup` proves exactly
`Langlands.GroupScheme.AffineWeilParabolicElementarySubgroupStatement.{u}`
for an arbitrary universe `u`.

Let `K/k` be a finite separable extension of arbitrary fields and let `G` be
a group scheme over `K` with the published `IsConnectedReductive G`.
The canonical equivalence `AffineWeil.rationalPointsEquiv k K G` maps
`parabolicElementarySubgroup (AffineWeil.groupScheme k K G)` onto
`parabolicElementarySubgroup G`, with the image expressed by `Subgroup.map`
along the equivalence's monoid homomorphism. These are the existing
constructions and geometric subgroup predicates from the target statement.

The implemented proof applies the published theorem
`affineWeilParabolicElementarySubgroup_of_radicalTransport` to the published
unconditional proof `affineWeilParabolicRadicalTransport`.
The latter proves preservation and descent of actual parabolic–geometric
unipotent-radical diagrams under finite separable affine Weil restriction,
including group-scheme isomorphisms commuting with both inclusions.
Its proof uses dynamic parabolics and radicals, descent of cocharacters,
and preservation of connected reductivity.

The reduction compares the two sets of generators. Descent and the commuting
isomorphisms identify the image of a generator over `k` with a generator
over `K` using `AffineWeil.rationalPointsEquiv_map`. Conversely, preservation
of a diagram over `K` and the inverse rational-point equivalence supply a
generator over `k` mapping to the original one. Equality of the generator
sets then gives equality of the generated subgroups by
`MonoidHom.map_closure`. The two imported modules document these arguments
in detail.

The provenance is internal composition of the two published theorems. The
source interpretation of the target is the derived consequence of
Borel–Tits, *Groupes réductifs* (1965), 6.17–6.19 and 6.21(i), printed
pp.111–112, documented in the target's Markdown. The proof retains all the
target's quantifiers and adds no premise: the fields and characteristic are
arbitrary. Its imports contain no local Kneser–Tits result or planned
consumer of that result.
