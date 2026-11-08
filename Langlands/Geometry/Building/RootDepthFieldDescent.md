# Field descent from actual depth-collection data

This internal unit applies `RootDepthCollectionData` to an arbitrary field
extension `K/k`, with both fields at universe `u`. The original torus is split;
the ambient group is affine and smooth, and its torus map is monomorphic.
Original opposite-factor pairs and an injective complete enumeration of the
original indivisible positive roots supply the published actual ordered-factor
descent theorem. No finite, separable, Galois or characteristic condition is
added to the extension.

The supplied collection data belong to the extended torus and actual extended
ambient group. They do not include reflection, opposite-root, compatibility,
nontriviality or an apartment. `fieldRestrictedRayDepthSubgroup` is the actual
subgroup preimage of each retained ray factor under `rationalExtend`. Thus the
primitive, doubled-only and identity cases are retained at their original real
depths.

Every upstairs retained ray subgroup lies in the corresponding primitive root
group. In the doubled-only case this uses the actual doubled root subgroup
inclusion. The published `orderedRootFactors_fieldDescend` theorem descends all
factors of an extended original point in the supplied order. Their preimage
memberships then follow from the retained equalities. Conversely extend each
original factor and apply the group homomorphism to its ordered product. This
proves `mem_orderedRayDepthProduct_fieldExtend_iff` without positivity or a full
root-datum valuation.

For a root selection upstairs, every original preimage factor belongs to the
subgroup closure of the union of the literal restricted filtration sets. Root
support reflection and the definition of literal restriction prove the
primitive and doubled-only cases. Injectivity of rational-point extension for
an affine group handles the identity case.

Finally assume the displayed closed-positive depth data, the doubled-depth
bound and the primitive/double cover. Collection identifies the upstairs
generated filtration subgroup with its actual ordered ray product. Descend
the factors as above and multiply their memberships in the original generated
subgroup. The reverse implication is proved directly on its original
generators. `mem_generated_fieldExtend_iff` therefore reflects membership in
the actual generated subgroup without any full upstairs lower-torus valuation
or any downstairs commutator axiom.

The proof adapts the internal collection and field-descent arguments in
`PositiveDepthFieldDescent`, using only the weaker displayed data. No new
literature assertion is claimed. Existence of the supplied collection data,
the remaining valuation laws, compatible apartment existence, metric building
geometry and the supplied-model building comparison are not established here.
