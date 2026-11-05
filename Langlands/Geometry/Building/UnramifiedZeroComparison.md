# Comparing unramified zero subgroups through torus norm images

This internal comparison isolates the group-theoretic assembly for the
independence part of Kaletha–Prasad, Lemma 2.6.24, for Definition 2.6.23(1)
(2023 book, printed pp.104–105, PDF pp.135–136; registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, read with
`kaletha-prasad-2024-corrections`). It applies to the actual
`UnramifiedZeroDatum F H` and rational-point subgroups at arbitrary universe `u`.

`zeroPoints_eq_of_torusIwahori_image_eq` proves equality when the two ambient
torus norm images agree. The simply connected images agree by the published
cover-independence theorem, so the defining subgroup joins agree.
`map_zeroPoints_eq_of_torusIwahori_image_eq` proves the corresponding comparison
under an ambient group-scheme isomorphism, using transport of the simply
connected image and preservation of joins by subgroup images.

`zeroPointsEquivOfTorusIwahoriImageEq` restricts that ambient isomorphism to an
isomorphism of the zero subgroups. Its coercion formula is proved by
`coe_zeroPointsEquivOfTorusIwahoriImageEq_apply`, so the subgroup isomorphism
agrees with the original map on rational points.

`map_zeroPoints_inner_eq` uses the elementary fact that an element of a subgroup
normalizes that subgroup. The published `rationalPoints_map_innerIso` identifies
the inner group-scheme automorphism with literal conjugation on rational points.
Consequently `zeroPoints_eq_of_sharp_conjugation` shows that conjugation by an
element of `E.simplyConnectedImage` carrying the ambient torus norm image to
that of `E'` gives `E.zeroPoints = E'.zeroPoints`: that element already belongs
to `E.zeroPoints`, so the transported subgroup equals the original subgroup.

Finally `zeroPoints_eq_of_sharp_torus_iso` accepts an isomorphism of the source
tori, a commuting conjugation triangle, and equality of the norm subgroups under
that isomorphism. The triangle identifies the two composed point maps; the
composition law for subgroup images gives the needed ambient-image equality.

These are derived internal assembly lemmas. They assume the indicated torus
norm-image compatibility and, in the sharp versions, a conjugating element in
the simply connected image. They do not prove existence of such a conjugator
or independence of the splitting field. Those remain required inputs to the
unconditional published independence statement.
