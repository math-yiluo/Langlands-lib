# Comparing represented subgroups on an etale cover

This internal construction supplies comparison of subgroup representatives on
an arbitrary etale cover of an arbitrary base scheme `S`, in every universe.
The cover and its members need not be quasi-compact, and the base need not be
affine, reduced or noetherian. The two subgroup inclusions must be monomorphisms
of relative schemes; they need not be closed or smooth.

`isIso_of_baseChange_etaleCover` detects invertibility of a group-scheme
homomorphism from invertibility after each actual base change in the supplied
cover. The published `TorusIsomorphismLocus.isIso_etaleImage`, whose hypotheses
do not require tori, descends each isomorphism to the open image of its etale
map. These open images cover `S`. The published open-cover reflection theorem
then proves that the original homomorphism is an isomorphism.

`SubgroupFunctor.range_eq_of_baseChange_etaleCover` assumes equality of the
two actual base-changed ranges on each member of the etale cover. Equality of
these subgroup functors is equality on every relative test scheme, including
nonreduced tests. The subgroup-intersection projection criteria in
`RelativeLevi.UnipotentRadicalRigidity` make both projections isomorphisms on
each cover member. Base change preserves the categorical pullback defining the
intersection. The preceding isomorphism reflection therefore makes both
original projections isomorphisms, proving equality of the original ranges on
every test scheme.

`SubgroupFunctor.isoOfEtaleCoverRangeEq` constructs an actual isomorphism
between the subgroup sources by uniqueness of representatives for that common
subgroup functor. Its `hom_comp` theorem says that the comparison followed by
the second inclusion equals the first inclusion. Monicity of the second
inclusion implies uniqueness of a compatible comparison.

The provenance is the composition of the published etale-image reflection,
Zariski isomorphism descent and uniqueness of subgroup representatives with the
internal intersection projection criteria. This module constructs no etale
cover or relative radical. Local radical comparison and local existence remain
separate inputs in an application to the relative unipotent radical theorem.
