# The zero-subgroup normalizer action over the maximal unramified field

This internal support module uses the original maximal-unramified field, its
integer-normalized valuation, every supplied `UnramifiedZeroDatum E`, and every
supplied full-compatible `BuildingData B` on the same group.

`torusIwahori_le_integerCharacterValuationKernel` applies the published norm
kernel bound for the prescribed spectral valuation and then uses equivalence
with the integer-normalized valuation. Thus the actual norm subgroup has unit
values for every rational character of the datum's torus.

`exists_zeroPoints_eq_simplyConnectedImage_sup_trivialNormalizer` conjugates
the maximal split subtorus contained in the datum's torus onto `B.S`, using
the published arbitrary-field maximal split torus conjugacy theorem. The
conjugated torus factors through the represented scheme centralizer of `B.S`.
Functoriality of the character kernel and full V6 make its norm subgroup act
trivially on the original apartment. The zero subgroup and simply connected
image are normal by the published commutator theorem, so conjugating the
original defining join gives the simply connected image joined with this
trivial-action normalizer subgroup.

`normalizer_mem_affineWeylGroup_of_mem_zeroPoints` and its subgroup-image form
retain the maximal-unramified simply connected normalizer assertion as an
explicit argument. Normality of the simply connected image turns the preceding
join into a product: write a zero-normalizer element as a simply connected
image element times a trivial-action normalizer element. The first factor is
also in the original normalizer. The actual source-building transfer in
`UnramifiedCoverNormalizerComparison` bounds its action by the ambient affine
Weyl group, while the second factor has identity action.
`zeroNormalizerWeylActionOfStatement` restricts the original action on the
actual zero-normalizer intersection to this affine Weyl group; its coercion
lemma records that the underlying action is unchanged.

These are derived constructions from named Library results, with no additional
literature assertion. They neither prove the simply connected normalizer
assertion nor the final affine-root fixer statement.
