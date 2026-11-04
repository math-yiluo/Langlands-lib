# Proper Borel subgroups through a split torus with a root

Author: Worker 1549.

This internal prerequisite works over an algebraically closed field `k : Type u`,
in every characteristic. The ambient group is pseudo-reductive and a split
torus maps to it with an actual relative root, defined using the adjoint
action on the Lie algebra. Neither pairwise dependence of roots nor uniqueness
of positive roots is assumed.

`not_isNormal_range_of_relativeRoot_of_isSolvable` proves that a smooth
connected solvable closed subgroup through which this torus map factors has
nonnormal all-test image in the ambient group. If its image were normal, the
published normal-solvable centrality theorem would make its inclusion central.
The prescribed factorization would then make the torus map central. The
published root restriction theorem rules this out in the presence of an actual
relative root. Affineness of the subgroup follows from its closed inclusion.

`not_isSolvableGroupScheme_of_relativeRoot` applies this obstruction to the
identity inclusion of the ambient group. Pseudo-reductivity provides the
smoothness and connectedness needed here, and the image of the identity is
normal on every test scheme. Consequently the ambient group is not solvable.
`not_isIso_of_relativeRoot_of_isSolvable` then rules out any isomorphism from
a solvable group scheme to this ambient group, using transport of solvability
along an isomorphism. This last assertion needs no closedness, smoothness or
connectedness assumption on the source, and no factorization of the torus
through it.

`BorelExistence.ProperBorelContainingData` retains an actual Borel group scheme,
its inclusion, the specified torus factorization and its equality, the Borel
property, and the fact that its inclusion is not an isomorphism.
`properBorelContainingDataOfRelativeRoot` constructs these data whenever the
given torus map is closed. It applies the published actual Borel-containing
construction to this smooth connected solvable torus, then proves properness
by the preceding obstruction. `exists_proper_isBorelPair_of_relativeRoot`
specializes to a split maximal torus and records the resulting actual proper
Borel pair and factorization.

The provenance is internal: the new obstruction combines the published
normal-solvable centrality and root restriction proofs. The actual Borel
choice uses the existing minimal coordinate-kernel-height construction in
`Absolute.BorelContaining`; its proof is imported unchanged.

This constructs the proper solvable subgroup needed in the rooted
algebraically closed case of the rank-one argument. It does not construct a
homogeneous quotient, bound its dimension, prove containment of a torus
centralizer in this Borel, or supply torus conjugacy. The unrestricted
`RankOnePositiveRootUniquenessStatement` remains a separate proof obligation.
