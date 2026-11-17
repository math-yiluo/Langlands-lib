# An affine-base isogeny criterion from a compatible torus isogeny

This internal derived module verifies the isogeny property of a supplied
homomorphism over an arbitrary commutative ring. Let `G` and `H` be
reductive group schemes over `Spec R`, with specified coordinate split
tori `i` and `i'` that are maximal on every residue-field fibre. Suppose
their coordinate root data `P` and `Q` satisfy `IsFibrewiseRootDatumOf`
and their finite root-index types have equal cardinality. Let `q : G ⟶ H`
and a torus isogeny `t` satisfy the actual square
`i ≫ q = CommGroupScheme.groupHom t ≫ i'`. Then `q` is an isogeny,
meaning a finite, flat, surjective morphism.

The definition `fieldImageIsoOfSplitTorusRestriction` constructs, for
every supplied field algebra `R → k`, the isomorphism from the actual
schematic-image group scheme of `q_k` to `H_k`. Its forward map is the
canonical schematic-image inclusion, as recorded by
`fieldImageIsoOfSplitTorusRestriction_hom`. It uses the field-fibre
isogeny theorem below to supply finiteness and equality of actual Lie
dimensions to `imageIsoOfFiniteFinrankEq`. This family of isomorphisms
concerns the actual schematic images formed after base change; no
commutation of global schematic-image formation with base change is
asserted.

`isIsogeny_algebraMap_of_split_torus_restriction_of_root_card_eq`
first proves this on the actual pullback along every supplied field
algebra `R → k`. The proof transports the base change of `t` through the
canonical split-torus base-change isomorphisms, obtaining an isogeny
between the coordinate split tori over `k`. The transported square is
the original square followed by functorial base change and cancellation
of these isomorphisms. Fibrewise maximality gives maximal tori on this
supplied field fibre; `IsFibrewiseRootDatumOf.field` gives its actual
root data, with the original root-index types. The field criterion
`isIsogeny_of_torus_restriction_of_root_card_eq` therefore applies.

`isIsogeny_of_split_torus_restriction_of_fibrewise_root_card_eq`
installs on each residue field the algebra structure determined by its
actual residue-field point. The preceding result then gives the
isogeny property on that exact residue-field pullback. The published
theorem `reductiveFibrewiseIsogeny` promotes these fibrewise isogenies
to an isogeny over `Spec R`.

The statements require no root-space freeness, localness, reducedness or
nontriviality of `R`, and impose no smoothness on the kernels. They
assume the compatible ambient homomorphism and the torus isogeny are
already given; constructing them is a separate obligation in the
affine split Isogeny Theorem.

The provenance is composition of the imported Library results. The
last step implements Conrad, *Reductive group schemes* (2014),
Proposition 6.1.10, in the verification of Theorem 6.1.16(1).
The registered source is `conrad-2014-reductive-group-schemes`.
