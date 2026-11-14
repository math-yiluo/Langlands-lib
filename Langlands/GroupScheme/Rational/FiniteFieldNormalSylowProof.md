# The finite-field normal Sylow torus criterion

`Langlands.GroupScheme.finiteFieldNormalSylowTorusProof.{u}` proves exactly
`Langlands.GroupScheme.FiniteFieldNormalSylowTorusStatement.{u}`.
Its proof term is the published theorem `finiteFieldNormalSylowTorus.{u}`
from [FiniteFieldBorelSylow](FiniteFieldBorelSylow.md). This is a focused
proof entry for the existing result, with no additional hypotheses.

The imported theorem applies
`finiteFieldNormalSylowTorus_of_sylowBorel` to the proved
`finiteFieldSylowBorel`. That classification identifies a maximal
defining-characteristic p-subgroup with the image of the actual rational-point
map of a geometric Borel radical. In the reduction, normality and maximality
absorb the opposite contracting subgroup's rational points into the given
subgroup, and hence into the Borel. The opposite intersection theorem then
makes those points trivial. The split-unipotent point count over the finite
field makes the opposite contracting subgroup trivial on every scheme test.
Signed parabolic comparison makes the Borel the whole group, and the
solvable reductive torus theorem gives the conclusion. The detailed reduction
is described in [NormalSylowBorelReduction](NormalSylowBorelReduction.md).

The proposition retains every published premise: an arbitrary finite field
`k : Type u`, a connected reductive `k`-group `G`, and a subgroup of
`rationalPoints G` that is a `ringChar k`-group, maximal among such subgroups,
and normal in the full rational-point group. The conclusion is `IsTorus G`,
including nonsplit tori. The proof uses the actual rational-point maps; no
geometric density of the finite rational-point set is assumed.

This module is derived entirely from the cited published Library proofs.
It adds a proof entry for the prerequisite isolated from the final normalizer
paragraph of Kaletha–Prasad Proposition 13.5.2; it asserts no local integral
model or building conclusion.
