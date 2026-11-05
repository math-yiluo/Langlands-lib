# Isomorphism invariance of torus norm subgroups with a common field

This internal comparison proves that an isomorphism of affine commutative group
schemes carries `torusNormIwahori k L v T` onto `torusNormIwahori k L v U`.
The groups use the same finite Galois extension `L/k` and valuation `v`.
The field and scheme universe `u` is arbitrary, and the valuation's value group
has an independent universe. No torus or splitting assumption is needed.

`torusNormIwahoriEquiv` restricts the induced rational-point isomorphism to an
isomorphism of these norm subgroups. Its coercion to ambient rational points is
the original point map, as proved by `coe_torusNormIwahoriEquiv_apply`.

The companion result `map_torusNormIwahori_eq_of_iso_comp` compares their images
in any ambient group scheme when the embeddings commute with the isomorphism.
The specialization
`UnramifiedZeroDatum.torusIwahori_map_eq_of_iso_of_field_eq` compares the torus
norm subgroups of two unramified zero data whose splitting fields are equal,
including data for different ambient group schemes.
This is a derived comparison for the norm-image construction in Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Definition 2.5.13 (printed p.90,
PDF p.121), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`.
The 1 November 2024 corrections, registered as
`kaletha-prasad-2024-corrections`, PDF pp.24–25, retain that construction.

The first proof applies the published `map_torusNormIwahori_le` to the
isomorphism and its inverse. Every target element is the image of its inverse
image, and the two group-scheme maps compose to the identity. The second proof
uses the commuting triangle on rational points and the composition law for
subgroup images. These results compare representations over a fixed extension;
they do not establish splitting-field independence or conjugacy of tori.
