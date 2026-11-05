# Closed generation by a normal subgroup and its full centralizer

This internal reduction supplies the closed-generation step in Worker 1566's
proof of generation by normal almost-simple subgroups. It assumes the two
proposition targets `SemisimpleRootGenerationStatement` and
`SemisimpleNormalRootDichotomyStatement`. Neither proposition is proved here.
The field is algebraically closed with arbitrary characteristic and universe.

The input consists of an actual semisimple group `G`, an actual split maximal
torus inclusion `t`, a smooth connected closed normal inclusion `h : H → G`,
and a closed subgroup inclusion `d : D → G`. Both the full range of `h` and
the full fixed subgroup of conjugation by `H` must be contained in the range
of `d`. The centralizer condition includes every test scheme and every
refinement; no smoothness of the centralizer or of `D` is assumed.

`range_eq_top_of_normal_and_centralizer` uses the dichotomy to put each
entire actual root subgroup functor in the range of `d`: the root is either
contained in `H` or contained in its full centralizer. The root-generation
premise then makes the range of `d` the entire functor of points of `G`.

`normalCentralizerGenerationIso` constructs an actual isomorphism `D ≅ G`
using the published uniqueness of representing group schemes. The closed
inclusion `d` and the identity of `G` represent the same full subgroup
functor. The companion equation `normalCentralizerGenerationIso_hom`
identifies the forward map with the original inclusion `d`.

The provenance is the internal composition of the two actual-root targets
with the represented-subgroup interface. The implemented proof is exactly
the two-case containment argument followed by uniqueness of representation.
The construction retains the chosen actual split maximal torus and both
unproved structural premises. It does not assert pointwise product
factorization by `H` and its centralizer, almost-simple decomposition, or
the unconditional almost-simple-generation target.
