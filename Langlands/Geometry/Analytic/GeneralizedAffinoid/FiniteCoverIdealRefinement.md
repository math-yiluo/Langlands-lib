# Compatible ideals under finite-cover refinement

This derived internal module reduces ideal effectiveness along an actual
refinement of finite full-domain covers. It uses the ideal locality theorem
and the actual bounded restrictions. It does not assume effectiveness for
the original cover.

`interCover` intersects every member of a finite cover with a supplied full
subdomain of its target. The first actual intersection projections form a
cover of that subdomain, with the same finite index set.

`IdealCompatible.on_test` extends pairwise intersection compatibility to any
full-domain test mapping to two components. Such a test factors through the
actual intersection. Composition of closed ideal extension proves the claim.

For a refinement `r` of a cover `c` by a cover `d`, `Refinement.idealFamily`
closedly extends each original ideal along the chosen refinement restriction.
The test-compatibility result proves compatibility of this refined family
and equality of closed extensions on every intersection of an original
component with a refined component.

The refined and original families have the same explicit global contraction.
One containment follows from composition of restrictions. For the other,
test each original ideal on the cover formed by its intersections with all
refined components. Pairwise compatibility and membership in the refined
ideals give membership in every closed extension on that cover; ideal locality
then recovers membership in the original ideal.

Finally, suppose effectiveness has been proved for the refined family.
On the same intersection covers, compatibility and the refined effectiveness
equations identify the closed extensions of the original ideal and of the
extended global contraction. The ideal extension order embedding detects
their equality. Thus `ideal_effective_of_idealFamily_effective` proves
effectiveness for the original family.

All algebras and maps are the stored presented algebras and actual bounded
restrictions. Arbitrary positive radii, trivial coefficient valuations,
nonreduced and zero algebras, empty spectra and empty finite covers are
retained. The proof is an internal combination of full-domain intersections,
closed-extension composition and finite-cover ideal locality; no further
source assertion or module descent theorem is used.
