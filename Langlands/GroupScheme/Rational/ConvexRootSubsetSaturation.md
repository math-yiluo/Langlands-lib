# Cone saturation and the reduced convex-root intersection reduction

This internal derivation uses the published relative-root system and the
intrinsic positive-multiple inclusion of root subgroup functors. Its final
result is the implication
`ClosedRootSubsetGroupIntersectionStatement.{u} →
ConvexRootSubsetGroupIntersectionStatement.{u}`. The full-root intersection
theorem remains a premise here; this module does not prove it or the
unconditional reduced-root intersection target.

For any ambient character set, `rootConeSlice_inf` identifies the slice of the
intersection of two pointed cones with the intersection of their slices.
`IsConvexRootSubset.inter` then uses closedness of the intersection of the
cones. No finiteness or root-system hypotheses enter these two lemmas.

`tmul_double_mem_pointedCone_iff` identifies the real tensor image of twice a
character with twice its image. Positive scaling preserves membership in a
pointed cone in both directions, so the two characters have equivalent cone
membership.

For an actual relative root system,
`HasRelativeRootSystem.mem_indivisible_or_eq_double` proves that every root is
indivisible or twice an indivisible root. If a root is divisible, the existing
crystallographic multiplier bound forces the divisor's multiplier to be two.
If that divisor were divisible again, the original root would be an integral
multiple of order at least four of an actual root, contradicting the same
bound. This argument retains the actual `HasRelativeRootSystem` hypothesis
and uses its published arithmetic consequence in `RelativeRootMultiples`.

`IsRootSubsetGroup.of_indivisible_coneSlice` uses this alternative to extend a
given minimal closed generated group from the indivisible-root slice of a cone
to its full-root slice. An added doubled root has its root subgroup contained
in that of the indivisible root, by `RelativeRoot.double_subgroup_le`. The
minimality condition transfers because the indivisible slice is contained in
the full slice. These assertions hold as subgroup functors on every test
scheme; closedness of the cone is unnecessary for this transfer.

The Prop-valued `ConvexRootSubsetGroupIntersectionReductionStatement` packages
the conditional implication. The theorem
`convexRootSubsetGroupIntersection_of_closed` proves it for an arbitrary field
in universe `u`, an actual connected reductive group, and a maximal split
torus. The published `relativeRootSystem` supplies the root-system predicate.
Choose the two closed cones from the supplied reduced-root convexity
hypotheses, and view their slices in all relative roots. The transfer lemma
applies to each of the two given generated groups, and to the third group
using the intersection cone. The full slices are convex and hence closed;
their intersection is convex by `IsConvexRootSubset.inter`. The assumed
full-root intersection theorem therefore gives precisely the required
`HasReducedPointIntersection` for the original three homomorphisms. The
reduced-test-scheme scope is inherited without strengthening it.

The source of this reduction is the explanation of the reduced reading of
Renard V.4.2(i) in the published `ClosedRootSubsetStatements.md`. This module
introduces no new literature premise. Its implementation uses the existing
root-system and root-subgroup results and spells out the cone saturation
argument, while leaving the substantial Borel–Tits intersection theorem
explicitly assumed.
