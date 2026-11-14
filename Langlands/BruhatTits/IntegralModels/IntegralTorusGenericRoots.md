# Generic roots and opposite pairs through an integral torus

This internal transport unit uses the actual `genericIso` and `generic_comm`
in supplied `IntegralTorusData T`. It works at arbitrary universe `u` over
a domain `R` with specified fraction field `K`. It changes the
parametrization of the acting torus while retaining the original ambient
generic group, every ambient point and the order of both opposite factors.

`genericHom_isMaximalSplitTorus` transfers maximal splitness from the supplied
generic inclusion `i : S → G` to `D.neutral.genericHom T.inclusion`.
Splitness and closedness transfer along the actual source isomorphism
`T.genericIso`. For maximality, any split overtorus factorization is
precomposed with its inverse; maximality for `i` makes that composite an
isomorphism, and composing back gives an isomorphism of the original factor.
No separate splitness or closedness of the integral torus is assumed.

For every integral character `χ`, `generic_subgroup_eq` identifies the
actual root subgroup functor for its base-changed character and generic
integral inclusion with the root functor for `T.genericCharacter χ` and `i`.
The equality holds on all relative test schemes. It specializes the
existing `RelativeRoot.subgroup_comap_of_transport` to the specified torus
isomorphism and the identity of the ambient group. When the ambient generic
group is affine, `generic_mem_relativeRoots_iff` gives the corresponding
equivalence of actual relative-root membership, by transport of Lie weights.

`generic_isOppositeFactorPair_iff` specializes
`RelativeRoot.isOppositeFactorPair_changeTorus_iff` to the same isomorphism.
It preserves the middle point and the two ordered ambient factors and
retains the complete normalizer-product condition. It does not impose
nonidentity, root membership or integrality assumptions.
`genericOppositeFactorPairsEquiv` packages this equivalence on the subtypes
of pairs. Its two maps retain the underlying pair by definition and change
only the proof of membership; both inverse laws are reflexivity.

If the integral torus is split, `T.genericCharacterEquiv` supplies an
integral character mapping to any given generic character. The present
lemmas then transport the root and opposite-pair data needed to apply
integral sufficiency to that character. They do not prove integral
opposite-factor sufficiency or the final descended facet root datum.
Their provenance is internal composition of the existing torus
identification and cross-torus transport APIs.
