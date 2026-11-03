# A split limit onto the centralizer intersection

This is an internal construction from the all-test dynamic limit and the actual
scheme-theoretic subgroup intersection. Let `j : H → G` be a closed subgroup
normalized by the range of a cocharacter `χ`, with `range j ≤ P(χ)`, and let
`z : Z → G` be a closed representative of `Z(χ)`. The ambient group is separated.

`subgroupCentralizerLimit` is a group-scheme morphism from `H` to the pullback of
`j` and `z`. On every test scheme it sends a point to its existing dynamic limit.
Closedness and normalization ensure that this limit remains in `range j`; the
separated limit theorem places it in `Z(χ)`. Naturality and the group laws come
from the published restricted limit homomorphism. The representation equivalences
turn this natural family into the displayed morphism of actual group schemes.

The first projection from the intersection into `H` is a section: a point of the
intersection centralizes `χ`, so its unique limit is itself. In particular the
limit is an epimorphism of schemes. The section also makes its map on underlying
topological spaces surjective, so connectedness of `H` passes to the
intersection. Over a field, unipotence of `H` also passes to the intersection by
`IsUnipotent.of_epi`, which uses the actual finite-representation definition of
unipotence. These assertions quantify over all test schemes and do not use
reducedness, perfectness, or a characteristic restriction.

This construction alone does not identify a geometric unipotent radical.
