# Products of actual p-divisible group morphisms up to isogeny

The actual projections and factor inclusions at each finite level
commute with the transition maps. They give `prodFst`, `prodSnd`,
`prodInl` and `prodInr` on the whole tower. The two coordinate
endomorphisms sum to the identity.

The latter equality also holds in the rational tensor Hom. It proves
that the two projections distinguish morphisms into the actual product
up to isogeny. `RationalHom.prodMap` adds the two composites through
the corresponding projection of the source and inclusion of the target.
Postcomposition with either target projection recovers the specified
coordinate map of the source. The resulting product maps preserve
composition and identity. On integral maps this operation agrees with
the integral product homomorphism at every level.

The split rigidifier in Rapoport–Zink (1996), §6.43, printed p. 309
(PDF p. 321), combines the primal rigidifier and the inverse of its
dual on the two actual factors. The rational product map is the
construction used to combine those two maps.
