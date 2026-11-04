# Constructible-set detection along affine-transition limits

This is an internal prerequisite for eventual fibre-property descent in
Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed pp. 5–6, Theorem 3.4(2). The source is
registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The constructible-set engine is a derived prerequisite, not that full
descent theorem.

`ConstructibleAffineLimitEmptyDetection` quantifies over an actual
cofiltered diagram of schemes with affine transition maps and an actual
limiting cone. At a quasi-compact quasi-separated stage, every
constructible subset whose inverse image in the limit is empty has
empty inverse image along some incoming transition. No transition map
is required to be injective or surjective.
The category of indices and its morphisms and the schemes lie in a
common arbitrary universe, as in the pinned affine-transition limit
theorem.

The proof inducts on constructible sets using the actual affine-open
basis. For an affine open U minus a finite union V of affine opens,
empty inverse image is the inclusion of the pullback of U in that of V.
Pinned Mathlib's `exists_map_preimage_le_map_preimage` detects this
inclusion at a stage; it uses compactness of U and affineness of the
transition maps. For a finite union, detect both parts, choose a common
incoming stage by cofilteredness, and pull their empty inverse images
back to that stage. The cofiltered cospan equality ensures the same
original arrow is used for both parts. The empty scheme is allowed;
the empty affine open supplies a nonempty basis index type.

Three consequences concern actual inverse images of constructible sets:
inclusion is detected by applying empty detection to the set difference;
equality is detected by applying it to the union of the two differences;
and a full inverse image is detected by applying it to the complement.
Both sets are required to be constructible in the inclusion and equality
results. In each result a single incoming stage and a single transition
arrow realize the conclusion. Finally,
`preimage_eq_univ_iff_exists_map_of_isConstructible` gives an equivalence
between the full inverse image at the limit and its occurrence at an
incoming stage. Its reverse implication uses naturality of the actual
limiting cone to factor the original cone map through that stage.

This does not establish constructibility of any fibre-property locus or
filtered descent of the geometric fibre condition. Those remain
separate obligations.
