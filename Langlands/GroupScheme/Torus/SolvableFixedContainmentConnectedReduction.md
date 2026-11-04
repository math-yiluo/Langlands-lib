# Algebraic-closure reduction for connected invariant solvable subgroups

This internal reduction keeps the exact hypotheses of
`SolvableFixedContainmentConnectedStatement` and reduces its proof to the same
assertion over algebraically closed fields in the same universe. The algebraically
closed assertion remains a separate proof obligation.

`AutomorphicAction.fixedSubgroup_baseChange` identifies the actual all-refinement
fixed subgroup after arbitrary scheme base change with the base change of the
original fixed subgroup. Its proof uses the universal acting point criterion,
the canonical comparison of the two product test schemes, naturality, and the
actual base-change point equivalence. It imposes no field, torus, smoothness, or
affineness hypotheses.

`SolvableFixedContainmentConnectedAlgClosedStatement` is the published target
with the additional instance `[IsAlgClosed k]` on the quantified field. It retains
uniform all-test solvability, actual automorphic action, all-test stability and
fixed-subgroup containment, every representing group scheme and map, and the
closedness and smoothness hypotheses.

`solvableFixedContainmentConnected_of_algClosed` pulls all data back along
`toAlgebraicClosure k`. Published results preserve the ambient group's smoothness,
affineness, connectedness and uniform solvability, the split torus, stability,
representation, closed inclusion and the representative's smoothness. The new
fixed-subgroup equality transports containment. Applying the algebraically closed
hypothesis makes the pulled-back representative connected. The projection from
that representative to the original one is surjective, since the field extension
is faithfully flat; connectedness descends along its continuous underlying map.

The provenance is internal: the reduction is derived from the published
base-change interfaces and geometric connectedness theorem. It does not claim to
prove either the algebraically closed assertion or the original connectedness
target without its stated hypothesis.
