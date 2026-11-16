# Subgroup-preserving local isomorphisms and stabilizer-valued discrepancies

This internal derived module isolates the cocycle step used after a local
isomorphism has been adjusted to identify chosen subgroup functors. All base
schemes, test schemes, parameter schemes and subgroup functors are arbitrary.

For an automorphic action `a` of `A` on `G`, `a.subgroupStabilizer F` consists
of the acting points whose restrictions preserve membership in `F` on every
further test. The equivalence of membership conditions gives a subgroup:
products compose the two membership equivalences, inverses reverse them,
and restriction retains the quantified condition. For the conjugation
action of `G` on itself, this is the published all-refinement normalizer
of `F`; the reverse conjugation is obtained using the inverse point.

`e.PreservesSubgroup F F'` says that each local isomorphism identifies the
points of `F` and `F'`, on all relative tests. Inverting a family reverses
this condition; refining its parameter retains it. Applying this membership
equivalence twice to the discrepancy equation shows that every representing
point preserves `F` on every refinement. Naturality therefore places every
value of an actual discrepancy cocycle in the subgroup stabilizer.

`LocalGroupIso.subgroupInnerCocycle` constructs a cocycle in a supplied
monic group-scheme representative of that stabilizer. It first constructs
the original natural cocycle from inner discrepancy and faithfulness, then
uses its proved membership to lift through the monomorphism. The companion
identities show that the lifted cocycle maps to the original one and is the
discrepancy for the restricted action. If the parameter is fppf over the base
and the lifted cocycle is trivial, twisting by a cobounding cochain and the
published fppf descent theorem give an actual isomorphism `G ≅ H`.

The provenance is internal: this uses the published natural local
isomorphism, faithful inner-discrepancy cocycle, cocycle lift, normalizer
and fppf descent interfaces. No existence of a group-scheme representative
for an arbitrary stabilizer is asserted. This module does not construct
Borel-preserving families, prove vanishing for Borel quotients, or prove
the quasi-split inner-form existence and uniqueness theorem.
