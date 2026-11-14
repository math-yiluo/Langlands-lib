# The induced base of a full-coroot root datum

This internal construction supplements `SimplyConnectedRootDatum`: for a root datum `P` with finitely many roots, a base `B`, and a finite quotient of the coweight lattice by the coroot span, `base P B` constructs a base on `rootDatum P` with precisely the same finite support.

The weight restriction map is injective under the finite-quotient hypothesis, so it carries the simple-root independence of `B` to the new datum. The simple coroots are the original coroots regarded as elements of their span; their independence follows by composing with the injective subtype map. For roots, the restriction map carries the positive and negative additive monoids into the new simple-root monoid. For coroots, mapping the new simple-coroot monoid by the subtype inclusion gives the original monoid, and injectivity pulls membership back. These verifications supply every field of the integral root-pairing base directly; no field-valued base constructor is used.

The construction is derived from the published full-coroot datum and elementary transport of linear independence and additive-monoid closure. It has no external source claim and makes no assertion that the original root datum is simply connected.
