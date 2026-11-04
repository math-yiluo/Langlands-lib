# Isogeny reduction to nilpotence or a noncentral semisimple tangent

The theorem `semisimpleIsogenyReduction` proves exactly the published
`SemisimpleIsogenyReductionStatement.{u}`. For every smooth connected affine
group scheme `G` over any field `k : Type u`, it constructs an actual
isogeny `G → G'` to a smooth connected affine group over the same field.
Either `G'` is geometrically nilpotent, or its algebraic-closure pullback
has a representation-semisimple tangent vector with proper actual Lie
centralizer. Every closed torus in `G'` lifts to a closed torus in `G`
through an isogeny, with the prescribed commuting square. No perfectness,
infinitude or characteristic restriction is imposed on the base field.

The proof uses the internal data type `SemisimpleReductionTarget G`.
An element records the target group, its smoothness, affineness and
connectedness, an isogeny from `G`, and the full closed-torus lifting
property. The identity is an element of this type. An outgoing central
isogeny to another smooth connected affine group produces another element:
ordinary isogenies compose, and the closed-torus lifting properties
compose using successive actual torus lifts. This construction does not
assert that the composite ambient isogeny is central.

Suppose no recorded target has either desired alternative. Then every
geometric semisimple tangent vector in every recorded target has full Lie
centralizer, and none of the targets is geometrically nilpotent. The
proof separates the two possible characteristics.

In characteristic zero, choose a maximal torus of the algebraic-closure
pullback of the identity target. It splits over that algebraically closed
field. Its tangent vectors map to semisimple vectors of the ambient group,
so all their Lie centralizers are full. The characteristic-zero centrality
theorem makes this torus map central. The actual quotient by this central
maximal torus is unipotent and gives a uniform lower-central-series bound
on every group of points. Specializing this bound to the identity scheme
test over the algebraic closure proves exactly the geometric nilpotence
of the original target, a contradiction. This avoids passing to a second
algebraic closure.

In characteristic `p > 1`, fix any split torus over the algebraic closure,
and consider all its maps to the geometric pullbacks of the recorded
targets. For each target over `k`, the exact centre-tangent kernel
construction supplies an outgoing central isogeny over `k` to another
smooth connected affine target. The new group is again recorded. After
base change, the same isogeny kills all tangent images of the chosen torus
map: these vectors are semisimple, their Lie centralizers are full by the
contradiction hypothesis, and the geometric centre-kernel theorem detects
precisely those vectors. Central isogenies remain central after base
change.

The split-root division termination theorem now says that every one of
these maps has empty actual adjoint root support. Its index type is the
full type of recorded targets, in `Type (u + 1)`; no finiteness of this
family is needed. The theorem keeps the split source torus fixed and uses
strict decrease of a nonzero integral character coordinate under division
by `p`. Apply it to a split geometric maximal torus of the identity
target. Empty roots give centrality, and the same central-maximal-torus
quotient and point bound give geometric nilpotence, again a contradiction.

Classical logic therefore yields a recorded target with one of the two
alternatives. Its fields supply exactly the isogeny, geometry and complete
torus-lifting clause of the published statement. All quotient groups and
isogenies remain over the original field; the algebraic closure is used
only for the tangent vectors and fixed-source root argument. The auxiliary
definitions and lemmas are internal constructions organizing the imported
results. The larger no-torus unipotence theorem remains a separate result.
