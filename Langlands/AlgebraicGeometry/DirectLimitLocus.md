# Full loci along a direct limit of rings

`specLimitCone` constructs the actual cone of spectra of a ring cocone, and
`isLimit_specLimitCone` supplies its universal property for a ring colimit.

This internal helper derives eventual fullness of a locus from fullness after a
ring colimit. The index type is any directed preorder, and the rings may be
arbitrary commutative rings. A specified starting index supplies nonemptiness.

`spec_preimage_eq_univ_iff_eventually_of_isOpen` applies Mathlib's
`exists_map_eq_top` to the inverse system of affine spectra obtained from the
ring diagram. The spectrum functor carries the colimit to its actual limiting
cone. Fullness is detected at an incoming stage and propagates to all later
indices by functoriality. Conversely, cocone naturality carries fullness at a
stage to fullness at the colimit.

`spec_preimage_eq_univ_iff_eventually_of_isConstructible` has the same conclusion
for a constructible set. Its detection step uses the published
`SchemeFiberGeometry.exists_map_preimage_eq_univ_of_isConstructible` from
[`ConstructibleAffineLimit`](ConstructibleAffineLimit.md). This module provides
adapters for the direct-limit group-scheme argument; it makes no new claim of
openness or constructibility for any particular locus.
