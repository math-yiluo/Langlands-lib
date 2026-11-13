# Actual Sylow subgroups from geometric Borel radicals

This internal construction concerns a connected reductive group scheme `G`
over a finite field `k`, at arbitrary universe `u`. Given a geometric Borel
embedding `i : B → G` and the ground-field unipotent radical `j : U → B`,
`geometricBorelRadicalSylow` constructs an actual Sylow `(ringChar k)` subgroup
of `G(k)`. Its underlying subgroup equals the range of the actual rational
point map of `j ≫ i`, as recorded by `geometricBorelRadicalSylow_toSubgroup`.

The proof first chooses a maximal split torus whose whole centralizer has a
closed torus representative, using the geometric Borel and the proved dynamic
centralizer reductivity and parabolic realization theorems. A generic
cocharacter gives a dynamic minimal parabolic and the actual dynamic Sylow
subgroup. Minimal parabolic conjugacy provides a rational point and an actual
isomorphism from this dynamic parabolic to the specified Borel. Transport the
specified radical back along that isomorphism. The published dynamic radical
comparison identifies its composite into `G` with the contracting subgroup on
every scheme test. Conjugating the dynamic Sylow therefore gives exactly the
specified radical point image.

`finiteFieldSylowBorel` proves the exact existing
`FiniteFieldSylowBorelStatement`. Finite-field quasi-splitness and ground-field
radical existence give one geometric Borel radical and its constructed Sylow.
Any maximal p-subgroup bundles as a Sylow subgroup; finite-group Sylow
conjugacy then realizes it by the same Borel and radical with conjugated
ambient embedding. Conversely, each specified radical image is maximal by
the constructed Sylow. The point conjugation is the map induced by the actual
scheme inner automorphism. All inputs used here are proved Library results;
no Borel classification or maximal-pro-p conclusion is assumed.

Finally, `finiteFieldNormalSylowTorus` proves the existing normal-Sylow torus
criterion by applying the published `finiteFieldNormalSylowTorus_of_sylowBorel`
reduction to this classification. That reduction uses the opposite contracting
subgroup and the finite-field split-unipotent point count; it makes no
Zariski-density assumption on finite rational points.
