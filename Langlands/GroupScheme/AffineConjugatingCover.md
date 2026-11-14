# Affine conjugating covers from etale conjugating covers

`HasAffineEtaleConjugatingCover i j` means that a single affine scheme over
the original base has an etale surjective structure map and carries an
actual point conjugating the two subgroup ranges after every refinement.
The definition does not assert that such a cover exists for every pair.

For monomorphic subgroup inclusions, the conjugacy relation of a supplied
point can be checked on any open cover of its test scheme. The proof pulls
the open cover back to each further test scheme. It checks the relation on
each resulting member and uses `mem_range_iff_openCover` to reflect membership
in either represented subgroup.

On any quasi-compact base, an etale cover carrying such conjugating points
refines to one satisfying the definition. Etale maps are open, so the original
cover is quasi-compact as a covering family. Mathlib's
`QuasiCompactCover.exists_hom` gives a finite affine refinement. Take its
disjoint union: finite disjoint unions of affine schemes are affine, and the
induced map remains etale and surjective. The component conjugating points
define a point on the disjoint union, and the preceding open-cover locality
theorem proves its conjugacy relation.

The range-equality variant starts with actual rational inner conjugators of
the base-changed subgroups on each etale cover member and uses
`isConjugatingPoint_iff_range_innerIso` and the rational base-change-point
equivalence to pass to original test points. The corresponding Borel corollary
first accepts `RelativeBorelEtaleLocalConjugacyStatement` as an explicit premise.
The final theorem applies its published proof
`relativeBorelEtaleLocalConjugacyStatement`, so relative Borel subgroups of a
reductive group over any quasi-compact base admit an affine conjugating cover
without an additional conjugacy premise.

This is internal refinement and gluing content based on Mathlib's finite
affine cover construction, the subgroup range APIs, and the published etale
Borel conjugacy theorem. It does not assert that the cover has a section over
the base or that a Borel cocycle is trivial. No represented subgroup
transporter is used.
