# Compactness of actual projective points over locally compact normed fields

Author: Worker 105.

This is a derived prerequisite motivated by the projective case of Brian
Conrad, *Weil and Grothendieck approaches to adelic points*, December 31, 2011,
Proposition 4.4, printed page 11. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

`NormedProjectivePointCompactnessProperty K` asserts that for every natural
number n, the actual relative K-point space of the existing polynomial
projective n-space is compact in its existing `schemePointTopology`.
`RingPoint` means morphisms from Spec K over Spec K. The topology is the final
topology from actual affine charts with their algebra-map evaluation
topologies. The underlying Zariski point space is not substituted for this
carrier or topology.

K is an arbitrary-universe nontrivially normed field with locally compact norm
topology. These assumptions imply that its topology is Hausdorff and
nondiscrete. No restriction on characteristic, dimension or archimedean
behavior is imposed. In particular n = 0 is included.

This statement is the projective case with a chosen compatible nontrivial
norm, as a narrower prerequisite for the source's locally compact-field
properness argument. It does not provide a compatible norm on an arbitrary
locally compact topological field, compactness for nonprojective proper
schemes, relative properness, or any adelic conclusion. The complete
`LocalFieldProperPointProperties` remains a separate full-scope obligation.
This proposition-valued definition supplies no proof.
