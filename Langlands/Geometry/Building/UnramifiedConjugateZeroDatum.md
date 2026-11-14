# Conjugation of the torus and splitting field in a zero datum

For every nonarchimedean local field `F`, every group scheme `G` over `F`,
every supplied `UnramifiedZeroDatum F G_K`, and every automorphism `σ` of
the maximal unramified field over `F`, `galoisTransport` constructs another
valid zero datum for the same ambient group `G_K`.

Its torus is the pullback of the original torus along `Spec σ`. The torus
inclusion is pulled back and then composed with the canonical descent
isomorphism for `G_K`. The maximally split maximal condition is transported
along those two isomorphisms. Its splitting field is the image of the original
embedded field under a chosen normal lift of `σ` to the fixed separable
closure. The previously established field-square comparison supplies torus
splitting over that image; the image is finite Galois over the unramified
field. Affineness follows from the pullback instance.

The derived subgroup, its inclusion, the simply connected cover, the covering
map, and its validity certificate are retained literally, since the ambient
group is the same. No compatibility among the chosen normal lifts, or action
law for transported data, is asserted.

`map_torusIwahori_le_galoisTransport` says that the actual section base-change
homomorphism sends the original torus Iwahori subgroup into that of the new
datum. It applies the bounded norm-image transport theorem to the restricted
field equivalence and its commuting square. The equality of the prescribed
spectral valuations under that equivalence gives the required valuation
equivalence. The result is an inclusion.

This is derived infrastructure for clause 2 of `UnramifiedZeroDescentStatement`,
using the published conjugated-field, torus and norm-image transport lemmas.
It does not assert Galois stability of the ambient zero subgroup or the full
descent theorem. The actual-point comparison and subgroup argument remain
separate obligations.
