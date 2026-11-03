# Borel images in supplied multiplicative quotients

This is an internal adapter between actual subgroup quotients and Borel
descent. All universes remain arbitrary.

For a monomorphism `i : B ⟶ G` over any base scheme, suppose `z : Z ⟶ G`
factors as `zB ≫ i`. The lemma `SubgroupFunctor.comap_range_of_factor`
identifies `(range z).comap i` with `range zB` on every scheme test, by
cancelling the monomorphism. Given fppf quotient homomorphisms `q : G ⟶ Q`
and `p : B ⟶ BQ` with these specified kernel ranges, and quasi-compact
`p`, `SubgroupFunctor.quotientHomOfKernelFactor` constructs the actual
homomorphism `BQ ⟶ Q` using fpqc homomorphism descent.

Over an algebraically closed field, `exists_borel_of_fppf_gm_quotients`
assumes `i` is Borel, `G`, `Q` and `BQ` are affine over the field,
`z` is a closed copy of `Gm`, and `zB ≫ i = z`. The two affine fppf
quotients by `range z` and `range zB` are supplied. It produces a Borel
embedding `j : BQ ⟶ Q`, the equation `i ≫ q = p ≫ j`, smoothness of both
quotient maps, geometric connectedness of `q`, a cartesian quotient
square, and the exact all-test equality `(range j).comap q = range i`.

Closedness of `zB` follows from closedness of its composite with `i`.
Affineness gives quasi-compactness of both quotient maps. Smoothness
follows from the smooth represented `Gm` kernel. Connectedness of `Gm`
and its finite type structure give geometric connectedness; transport to
the actual kernel and the connected-kernel theorem give geometric
connectedness of `q`. The factorization gives exact compatibility of the
two actual kernels and containment of the ambient kernel in `B`.
`quotientSubgroupHom_isClosedSubgroup`,
`quotientSubgroupHom_isPullback`, and
`quotientSubgroupHom_comap_range` then give the actual closed embedding,
cartesian square and inverse-image equality.
`isBorelSubgroup_of_quotient_square` supplies the full Borel property.

For smooth connected `G`, the corollary
`normalizer_borelRange_eq_of_supplied_fppf_gm_quotients` combines this
construction with the existing smaller-Lie-dimension normalizer adapter.
Its smaller-group induction hypothesis is explicit.

This module constructs neither quotient group. Centrality is unnecessary
once both fppf quotients are supplied. Their existence, the remaining
induction branches, and the exact `BorelNormalizerStatement` remain
separate obligations. The provenance is the displayed factorization and
the imported kernel, quotient, Borel descent and normalizer lemmas.
