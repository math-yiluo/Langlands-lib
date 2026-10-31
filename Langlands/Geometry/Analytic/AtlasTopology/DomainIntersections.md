# Intersections of subspaces covered by contained net members

This module constructs finite relative refinement witnesses for intersections
of subspaces covered locally by contained members of a fixed net. It works
in an arbitrary topological space, with no compactness, Hausdorffness or
openness hypotheses.

`intersectionFamily τ υ` is the family of actual sets `U ∩ V`, with `U`
from `τ` and `V` from `υ`. The intersection family of two singleton
families is the singleton of their intersection.

`isQuasinet_restrictedFamily_iff` identifies the quasinet condition on an
actual subspace `S` with `LocallyRefines τ {S}`. In the forward direction
the finite witness sets in `S` are mapped into the ambient space by subtype
inclusion. Each image is precisely its original contained member. In the
reverse direction the original witnesses are pulled back along inclusion.
Mathlib's equality between the image of a subspace neighborhood filter and
the ambient relative neighborhood filter transfers the neighborhood
condition in both directions.

`LocallyRefines.intersectionFamily` intersects two finite relative
neighborhood witnesses. The new family is the image of their finite
Cartesian product under set intersection. Every witness contains the
point and is contained in the required intersection. Its union is the
intersection of the original finite unions, which is a neighborhood
relative to the intersection of the two original sets.

`IsNet.locallyRefines_intersectionFamily` translates the defining
pairwise-intersection quasinet axiom into finite relative refinements by
original members. Combining it with the preceding finite construction and
the published transitivity of relative local refinements proves
`IsNet.isQuasinet_restrictedFamily_inter`: if the contained original
members form a quasinet on each of `S` and `T`, they form a quasinet on
`S ∩ T`. The proof takes two successive finite refinements; it does not
assume that intersections of original members are themselves members.
`IsNet.restrict_inter` then derives the full net on the intersection from
the published net restriction theorem.

These are internal consequences of the quasinet, net and induced-subspace
conventions in Berkovich, *Étale cohomology for non-Archimedean analytic
spaces* (1993), registered as `berkovich-1993-etale-cohomology`, section 1.1,
printed pp.13–14 / PDF pp.10–11. They are derived topological infrastructure
for original-chart subspace atlases. This module constructs no new
affinoid algebras, arbitrary analytic domains, atlas extension or site.
