# Simple-root scaling for an actual split pinning

Author: Worker 1354. The proof assembly was supplied in the task context by
Workers 1467 and 1416.

`Langlands.GroupScheme.pinnedRootScaling` proves exactly
`Langlands.GroupScheme.PinnedRootScalingStatement.{u}`, as defined in
[`PinnedRootScalingStatement`](PinnedRootScalingStatement.md).
The universe is arbitrary, and all the statement's binders are retained:
an arbitrary field, the supplied actual affine group scheme, its supplied
split pinning, and any tuple of units on its simple-root support.

The implemented proof introduces these binders and takes
`p.rootScalingIso c` as the existential automorphism.
`p.rootScalingIso_inclusion c` proves that its restriction to the supplied
torus is the identity. `p.rootScalingIso_rootVector c` supplies the equation
for every supplied simple-root vector using the actual linear differential
`Lie.targetMapLinear`. These are exactly the two conjuncts in the named
statement.

This is an internal derived corollary of Worker 1467's
[`RootScalingAutomorphism`](RootScalingAutomorphism.md).
That construction evaluates the descended action of the simple-root split
torus at the point with coordinates `c`. Its
[`RootScalingTorus`](RootScalingTorus.md) input obtains this action by
factoring conjugation through the fppf projection whose character pullback
sends coordinate characters to the supplied simple roots. Centrality of the
full scheme-theoretic kernel permits descent. The
[`AutomorphicActionPointIso`](../AutomorphicActionPointIso.md) helper realizes
evaluation as an actual group-scheme isomorphism and identifies its
differential. The imported construction proves torus fixation on every test
scheme and derives the vector equation from the corresponding coordinate
weight spaces and character values.

The proof adds no field, characteristic, perfectness, central-rank or
root-nonemptiness hypothesis. It chooses no rational lift through the supplied
torus. This module adds only the exact scaling theorem; the source statement
and its dependencies are unchanged.
