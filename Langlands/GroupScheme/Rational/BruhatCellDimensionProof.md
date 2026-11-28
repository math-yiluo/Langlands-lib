# The relative-root dimension formula

`Langlands.GroupScheme.rationalBruhatCellDimension` proves
[`RationalBruhatCellDimensionStatement`](BruhatCellDimensionStatement.md):
for a connected reductive group \(G\) over a field \(k\), a maximal
\(k\)-split torus \(T\), a cocharacter \(\nu\) of \(T\) and a point \(n\)
of the normalizer of \(T\), the intersection
\(C=U(\nu)\cap nU(-\nu)n^{-1}\) is smooth over \(k\) of relative
dimension

\[
\sum_{\substack{\alpha\in\Phi(G,T)\\
                 \langle\alpha,\nu\rangle>0\\
                 \langle w^{-1}\alpha,\nu\rangle<0}}
     \dim_k\mathfrak g_\alpha .
\]

The proof uses only that \(G\) is smooth and affine and that \(T\) is a
split torus embedded as a closed subgroup. It does not use the
genericity hypothesis on \(\nu\), the maximality of \(T\) or the
reductivity of \(G\).

## The intersection as a meet of unipotent functors

`BruhatCell.factor` is by definition the scheme-theoretic intersection
`subgroupIntersection (v ≫ (G.innerIso n).hom) u` of the conjugated
inclusion of \(V=U(-\nu)\) with the inclusion of \(U=U(\nu)\).
The normalizer point \(n\) sends \(-\nu\) to the cocharacter
\(\xi\) = `cocharacterAut (normalizingAut i n) (-ν)` of \(T\).
By `groupHom_cocharacterAut_comp` and
`groupHom_neg_comp_eq_oppositeCocharacter`, the composite of \(\xi\) into
\(G\) is the inverse cocharacter defining \(V\) followed by conjugation
by \(n\). Transport of the unipotent functor along this inner
isomorphism (`unipotent_eq_comap_of_iso`) shows that the conjugated
inclusion of \(V\) represents the \(\xi\)-unipotent functor. By
`isRepresentedBy_subgroupIntersectionHom`, the closed inclusion of \(C\)
represents the meet of the \(\xi\)- and \(\nu\)-unipotent functors.

## Smoothness and connectedness

`dynamicUnipotentSemigroupComparison_of_semigroupRealization`, applied
to \(\nu\) and to \(\xi\), identifies each unipotent functor with the
semigroup subgroup of the torus conjugation action for the characters
strictly positive on that cocharacter. The group \(V\) is smooth by
`dynamicSmooth`. The closed semigroup intersection theorem
`smooth_subgroupIntersection_semigroup` then gives smoothness of \(C\).

The common torus acts on \(C\) by `unipotentIntersectionTorusAction`.
Its restriction along \(\nu\) is compatible with the inclusion of \(C\)
and the conjugation action of \(\nu\) on \(G\)
(`unipotentIntersectionTorusAction_isEquivariant`). The closed
equivariant inclusion identifies its identity-limit functor with the
pullback of \(U(\nu)\), which is the full subgroup on every test scheme
because \(C\) lies in \(U(\nu)\). Connectedness of an affine scheme that
represents an identity-limit functor
(`AutomorphicAction.Affine.connectedSpace_of_isRepresentedBy_unipotent`)
then gives connectedness of \(C\).

## The Lie dimension

`hasLieImage_semigroupSubgroup_inf` identifies the tangent submodule of
the meet with the sum of the ambient adjoint weight spaces for the
characters in both semigroups. Representability identifies its finrank
with the Lie finrank of \(C\)
(`finrank_tangentSubmodule_eq_of_isRepresentedBy`).

Every character in both semigroups is nonzero. A character whose weight
space vanishes contributes the zero submodule, so the sum is over the
finite set of relative roots satisfying the two positivity inequalities.
The split-torus weight decomposition
(`isInternal_weightSpace_of_isSplitTorus`) makes these subspaces
independent, and their finranks add by `finrank_biSup_eq_sum`.

The pairing formula `latticePairing_cocharacterAut_normalizingAut`
gives \(\langle\alpha,\xi\rangle=-\langle w^{-1}\alpha,\nu\rangle\).
Thus the two strictly positive pairings select precisely the roots in
the asserted formula. Finally a smooth connected affine group has
constant smooth relative dimension equal to its Lie finrank
(`SubgroupProductOrbit.smoothOfRelativeDimension_lie_dimension`).
