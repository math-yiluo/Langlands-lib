# Promotion of Borels from closed overgroups

Worker 1358.

This module gives an internal reduction needed when a fixed split torus lies
in a parabolic subgroup. It uses the published definition of Borel subgroup,
its proved isomorphism transports, and rational conjugacy with an isomorphism
of source groups. It does not prove Borel conjugacy, geometric connectedness
of parabolics, or the fixed-torus cocharacter classification.

For a field `k`, `BorelSubgroupsAreConjugate P` says that every two embeddings
satisfying `IsBorelSubgroup` in `P` are related by `SubgroupConjugate`: there is
a `k`-point of `P` and an isomorphism of their source groups satisfying the
conjugacy equation. This is an explicit hypothesis, not a structure theorem
included in the definition of parabolic subgroup. It is invariant under
isomorphism of the ambient group.

`IsBorelSubgroup.of_comp` proves that an ambient Borel factoring through a
closed subgroup is a Borel there. Its smoothness, connectedness and solvability
are properties of the same source. Closedness follows by cancelling the
closed overgroup inclusion. Every admissible overgroup inside that subgroup
also gives an admissible overgroup in the ambient group, so ambient maximality
proves the required maximality.

`IsBorelSubgroup.of_subgroupConjugate` and
`SubgroupConjugate.isBorelSubgroup_iff` prove that rational conjugacy preserves
and reflects Borel structure. The proof transports first through the inner
automorphism of the ambient group and then through the inverse of the source
isomorphism, using `Absolute.BorelTransport`.

Finally, `BorelSubgroupsAreConjugate.isBorelSubgroup_comp` assumes a closed
inclusion `i : P ⟶ G`, conjugacy of Borels in `P`, and one factorization
`b' : B' ⟶ P` whose composite with `i` is a Borel of `G`. It proves that the
composite of every Borel of `P` with `i` is a Borel of `G`. The proof first
restricts the known ambient Borel to `P`, conjugates the given Borel to it
inside `P`, and postcomposes this actual conjugacy with `i`. Conjugacy
invariance then transfers ambient Borel structure. The argument works over
any field; it neither asserts nor uses a rational conjugacy theorem over an
arbitrary field.

The result isolates a consumer obligation for geometric fixed-torus Borel
construction. To use it for a geometric parabolic, one must still provide the
actual conjugacy hypothesis over the field under consideration and any
connectedness hypotheses needed by a theorem proving that conjugacy. No
unproved classification proposition is used as a proof.
