# All five axiom families on supplied actual anisotropic data

This is an internal assembly of proved constructions on supplied actual
`ParahoricBuildingData G` for an anisotropic group. It constructs a
polysimplicial realization and an apartment splitting with exactly the
seven predicates representing the five axiom families requested by
`RootValuationBuildingConstructionStatement`. It retains the supplied
parahoric data as a hypothesis. Consequently it proves neither the
unrestricted construction statement nor existence of those data, even in
the anisotropic case.

The new topological step proves the existing KP Axiom 4.1.2. The preceding
actual quotient construction makes the anisotropic reduced building a
subsingleton. The published `IsAnisotropic.rationalCommonNormKernel_eq_top`
puts every rational point in the actual common norm kernel. Thus every
original norm-one point stabilizer is the entire rational-point group.
This is open in exactly `rationalPointTopology F G.X`. The published
`anisotropicCompactness_proof` makes the entire point group compact in
that same topology, and
`isAlgebraicallyBounded_of_isCompact` gives precisely KP algebraic
boundedness. The result holds at every original quotient point and has no
extra topological or boundedness premise.

The existing empty-factor realization proves all one-group clauses of
Axiom 4.1.1. The actual derived-subgroup splitting constructed from the zero
datum proves every Axiom 4.1.4 field. Empty actual relative roots discharge
AS 1 without a reflection case; the earlier normalized empty-root
apartment construction proves V 6, V 7 and AS 2–AS 5, and the actual
root-free quotient geometry proves AS 6. The explicit trivial Weyl datum
proves all six fields of the existing Axiom 4.1.9 predicate on the original
`zeroSubgroup` and facets. These steps import the existing predicates and
their proved anisotropic specializations; they introduce no replacement
quotient, action, topology, roots, centralizer or normalization.

`anisotropicFiveAxiomData` packages the realization and splitting together
with all seven proofs at the original universe `u`. Its type states each
original predicate explicitly. The data and witnesses therefore satisfy
the requested five-axiom conclusion for this supplied anisotropic datum.
Unrestricted actual-data existence, groups with nonempty relative roots,
and the general descent and comparison constructions remain obligations
of the parent task.
