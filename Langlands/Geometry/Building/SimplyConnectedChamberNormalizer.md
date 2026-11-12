# Chamber stabilizers for a simply connected ambient group

This supporting module proves the chamber-normalizer step used by the Iwahori
decomposition argument when the supplied ambient group `G` is simply connected.
It is a derived consequence of the published apartment axioms and affine chamber
geometry, not an additional axiom or a proof of the general reductive case.
The proposition `SimplyConnectedChamberNormalizerStatement` quantifies over all
nonarchimedean local fields, actual supplied parahoric data, chambers, and
normalizer points at an arbitrary universe. Its theorem
`simplyConnectedChamberNormalizer` proves that a chamber-preserving point in
`P.normalizerZeroComponent` belongs to `P.normalizerZero` when `G` is simply
connected.

The first lemma applies `affineChamberSimpleTransitivity` to a chamber twice.
Both the given normalizer action, assumed to lie in the affine Weyl group, and
the identity preserve this chamber, so uniqueness makes their actions equal.
The second lemma obtains this affine Weyl membership from the simply connected
clause of AS 5 in `SatisfiesApartmentAxioms`.

The last lemma restricts to `P.normalizerZeroComponent`. The published kernel
comparison `normalizerAffineEquiv_eq_one_iff_of_mem_normalizerZeroComponent`
then identifies its trivial action
with membership in `P.normalizerZero`. Its centralizer-intersection hypothesis
is discharged by the second component of
`ZeroSubgroupDatum.minimalLeviZeroComparison`, converted by
`coverImageCentralizerNormKernel_of_intersection`.

This is derived content: the proposition packages a special case of the
chamber-stabilizer step in the Iwahori decomposition argument. Its meaning and
proof use the existing Library definitions and theorems named above. It does
not introduce a new translation of an assertion from the literature.
