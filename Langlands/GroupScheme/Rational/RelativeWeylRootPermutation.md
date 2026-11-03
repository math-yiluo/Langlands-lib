# The actual relative Weyl permutation action on roots

This internal auxiliary module restricts the published full character-lattice
action of the actual quotient `relativeWeylGroup i = N(k)/Z(k)` to the existing
relative-root subtype. The ambient field and universe are arbitrary, the group
is affine, and `i` is a monomorphism. The permutation construction requires no
splitness, reductivity, maximality, root-system or finiteness premise.

`relativeWeylRootPermutation` is a group homomorphism to permutations of the
actual character-valued roots. Preservation of roots follows by quotient
induction from the published normalizer action. The inverse permutation is
given by the inverse quotient class. The evaluation theorem identifies this
action with `relativeWeylCharacterAction` on each root.

`relativeWeylRootPermutation_eq_one_iff` says exactly that a quotient class
acts trivially if and only if it fixes each actual root. For a split torus,
`IsSplitTorus.relativeWeylRootPermutation_ker` identifies its kernel with the
kernel of the published rational root-span action. This uses the existing
`IsSplitTorus.relativeWeylAction_mk_eq_one_iff`, whose proof uses injectivity of
rationalization on a split-torus character lattice and the definition of the
root span. Neither kernel is asserted to be trivial.

When the ambient group is also locally of finite type and the torus is split,
the published root-support finiteness theorem makes the permutation group
finite. The first isomorphism theorem makes the quotient by its kernel finite.
The kernel equality then gives finiteness of the image of
`relativeWeylAction`. `relativeWeylActionRangeFintypeOfIsSplitTorus` constructs
a finite enumeration of that existing image subgroup.

`IsSplitTorus.finite_relativeWeylGroup_of_action_injective` additionally assumes
injectivity of the root-span action and then concludes finiteness of the
acting quotient. Its hypothesis records the separate faithfulness obligation;
the module does not prove it.

The provenance is internal: all claims follow from the published actual
actions, root-support finiteness and elementary permutation and quotient-group
arguments. The empty root set is allowed. This proves finite image, and leaves
faithfulness, unconditional finiteness of the acting quotient itself, root
reflections and the exact standard-parabolic order statement as separate
obligations.
