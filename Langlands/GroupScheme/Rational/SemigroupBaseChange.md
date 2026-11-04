# Actual semigroup subgroups under field extension

This internal comparison uses the actual character pullback, external torus
action, dual-number tangent images, and all-test subgroup functors. The fields
`k` and `K` lie in an arbitrary common universe.

`characterSemigroupBaseChange b S A` is the image of the additive subsemigroup
`A` under character pullback. It is a positive semigroup image: no zero is added.
The membership formula is an image witness, and positive generation commutes
with this operation by the image-of-generated-semigroup lemma.

`AutomorphicAction.IsStable.baseChange` transports stability on every test
scheme through the actual pullback point equivalence. For an affine ambient
group, `IsSmoothConnectedClosed.baseChange` transports a smooth connected closed
representative through scheme pullback. Closedness and smoothness persist under
base change; connectedness follows from the published geometric-connectedness
theorem for smooth connected affine groups over fields. Closedness of the
representing inclusion supplies its source's affineness.

For an affine locally finite-type ambient group and a split acting torus,
`extendedLieSubmodule_semigroupWeightSpan` identifies the extended original
selected weight span with the selected span for the pulled-back action and
image semigroup. Extension commutes with the submodule supremum; the external
action weight comparison identifies each summand, and image witnesses identify
the two indexings. Every character is allowed, including zero when it occurs.

If the ambient group is also smooth, `semigroupSubgroup_baseChange` proves
equality of the actual generated subgroup functors. Take a smooth connected
closed representative of the original generated subgroup. Its scalar extension
is again smooth connected closed and stable. The tangent-image comparison
identifies its exact Lie image with the transported selected span. The published
uniqueness theorem for smooth connected stable closed subgroups with that exact
Lie image then identifies it with the generated subgroup after extension.
`isRepresentedBy_semigroupSubgroup_baseChange` transports any supplied
representative by this equality. The equality is on all scheme tests and does
not assume reduced test schemes.

These are internal consequences of the actual weight and tangent base-change
comparisons, geometric connectedness, and the existing geometric semigroup
realization and uniqueness results. They do not require solvability or
connectedness of the ambient group. They supply the semigroup comparison for
scalar descent of an ordered product; they do not supply a compatible solvable
decomposition or the full ordered semigroup product theorem.
