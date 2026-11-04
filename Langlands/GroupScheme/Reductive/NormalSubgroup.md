# Reductivity of smooth connected normal closed subgroups

Worker 1372. Internal consequence of ambient normality of the radical,
radical existence, monomorphism cancellation and geometric connectedness
under field extension.

For the algebraically closed constructions, let `k : Type u` be
algebraically closed, let `G` be smooth with
`HasTrivialUnipotentRadical G`, and let `H` be smooth, connected and affine.
Let `i : H ⟶ G` be a closed inclusion with normal range on every test
scheme, and let `s : V ⟶ H` be a supplied unipotent radical. These are the
common hypotheses of `normalSubgroupTrivialIso`, its composite equation,
and `HasTrivialUnipotentRadical.of_normalSubgroup` below. Triviality of the
ambient ground-field radical alone does not supply smoothness of `G`.

This module constructs the actual isomorphism
`IsUnipotentRadical.normalSubgroupTrivialIso` from a supplied subgroup
radical to the trivial group scheme when the ambient ground-field radical
is trivial over an algebraically closed field. Its composite with the
unit inclusion is the original radical inclusion. The proof first shows
that the radical range is trivial on every test by killing the composite
normal radical in the ambient group and cancelling the closed subgroup
inclusion.

`HasTrivialUnipotentRadical.of_normalSubgroup` chooses a radical of the
smooth connected affine subgroup and uses its greatest property to show
that every smooth connected unipotent normal closed subgroup is trivial.

`IsConnectedReductive.of_normalSubgroup` proves reductivity of a smooth
connected normal closed subgroup of a connected reductive group over any
field in universe `u`. The subgroup is affine because its inclusion is
closed. After extension to the algebraic closure, smoothness, affineness,
closedness and normality persist; connectedness follows from geometric
connectedness of finite type connected group schemes. The ambient
geometric radical is trivial by the definition of reductivity, so the
preceding algebraically closed theorem proves the required geometric
radical triviality of the subgroup.

All subgroup ranges and normality assertions quantify over all test
schemes. The construction does not prove the reverse radical-intersection
containment in a nonreductive ambient group.
