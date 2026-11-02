# Actual points of relative affine pullback cones

This is derived infrastructure for the fibre-product axiom in Brian Conrad,
*Weil and Grothendieck approaches to adelic points*, December 31, 2011,
Proposition 2.1 and its proof, printed pages 2–3. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The source identifies points of a scheme fibre product with compatible pairs;
this module supplies that comparison for arbitrary actual relative cones and
relates it to the existing global-section construction.

Fix commutative rings R and S and an R-algebra structure on S. Both rings and all
schemes here have universe `u`. The point carrier `RingPoint R X S` is the
actual morphism set from `Spec S` to X in the category of schemes over `Spec R`.
No topology or finite-type condition is assumed in this module.

`affineSchemePullbackPointComparison` sends a point of the vertex of an actual
pullback cone to its compositions with the two legs. Its codomain consists of
pairs of actual relative points with equal composite to the common target.
The comparison is defined for any cone. Given its limit property,
`affineSchemePullbackPointEquiv` is a bijection: its inverse is the categorical
pullback lift. The factorization equations prove the right inverse, and the
limit's uniqueness proves the left inverse. The universal property is in all
schemes over the base, so no finite-type assumption on `Spec S` is involved.
These first constructions do not need affineness.

For affine factor schemes and common target,
`affineSchemePointPair_compatible_iff` expresses compatibility through the
actual global-section pullbacks, using naturality and injectivity of the
global-section point equivalence. `affineSchemeCompatiblePairEquiv` applies
the actual point equivalences to both components. Its inverse applies their
inverses; the compatibility equivalence proves that the inverse lands in the
required subtype. The point on the common target is free to vary: no fixed
algebra structure on S over that target's coordinate ring is assumed.

When the cone vertex is affine as well,
`affineSchemePullbackPointComparison_coordinates` proves the commuting
comparison with the actual coordinate-algebra cocone
`affineCoordinatePushout R c`. The two component equalities are precisely
the naturality of the global-section point equivalence for the two cone legs.
If the original cone is limiting, the already constructed
`affineCoordinatePushoutIsColimit` proves that this cocone is a pushout.

This module constructs the set comparisons and proves their compatibility. It
does not assert a homeomorphism, the four topology axioms or their
characterization; those require separate statements and proofs.
