# Effective affine descent of monic subgroup inclusions

This internal derived module extends the overlap and affine descent
constructions for closed subgroups to monic subgroup inclusions. Closedness is
not needed to construct the descent datum; equality of the ranges on every test
scheme identifies the representing source group schemes.

For an ambient group-scheme datum `D` and a monic inclusion `i`,
`Datum.monicSubgroupOverlap` uses
`SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy` to construct the actual
source overlap isomorphism. `monicSubgroupOverlap_fac` records its compatibility
with the inclusion. `cocycle_of_monicSubgroup_lift` pulls this equation back to
the triple overlap. After composition with the third pulled-back inclusion,
the desired source cocycle is the ambient cocycle. Pullback preserves
monicity, so cancellation proves the source cocycle. Thus
`Datum.monicSubgroup` constructs the complete datum, and
`compatible_monicSubgroup` makes the inclusion a morphism of data.

`exists_affine_monic_descent_of_overlap_range_eq` assumes an affine base and an
affine flat surjective cover, together with an affine source subgroup and a
monic inclusion into the pulled-back ambient group. Equality of the two
overlap ranges is the only invariance input. The imported affine group-scheme
effectivity theorem constructs the descended affine group scheme; actual
morphism descent constructs its arrow to the original ambient group.
Faithfulness of pullback detects that this arrow is monic. An actual
pullback isomorphism recovers the supplied inclusion by an exact equality of
group-scheme arrows.

The ambient group need not be affine. The base and cover schemes and the
source group scheme are affine hypotheses of the effectivity conclusion.
No smoothness, parabolicity or parameter-space existence is asserted here.
The proof generalizes the implemented cancellation argument in
`Descent.ClosedSubgroups` and uses only the imported actual affine effectivity,
representing-source comparison and faithful pullback results. This is its
internal provenance; it introduces no additional external assertion.
