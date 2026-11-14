# Bounded torus norm images under field isomorphisms

This derived helper specializes the coefficient-square norm transport to two
compatible field isomorphisms `e : k ≃ K` and `f : L ≃ M`. The vertical extensions
`L/k` and `M/K` are finite Galois extensions. The four fields have the same
arbitrary universe.

`fieldIsoSquareRationalExtend` packages the existing square transport as an
actual point homomorphism with these horizontal algebra structures internal
to its definition. It first extends from `L` to `M` along `f`, then uses the
two tower comparisons to reach the iterated base change along `e` and `K → M`.
This construction requires neither finite dimensionality nor Galoisness.

For an affine commutative group scheme `T/k` and valuations `vL`, `vM` whose
pullbacks along `f` are equivalent, the theorem
`map_torusNormIwahori_le_fieldIso_square` sends the actual bounded norm image
of `T` into the bounded norm image of its base change along `e`. The point map
is the existing scheme section base-change homomorphism.

The proof equips the horizontal field isomorphisms with algebra structures
locally, constructs the common scalar algebra using the commuting square, and
transfers finite dimensionality and Galoisness along the isomorphisms.
Valuation invariance for the top horizontal extension follows because every
automorphism over a surjective field map is the identity. The result then
follows from `map_torusNormIwahori_le_iso_square` and the equality between
section base change and rational scalar extension.

The auxiliary horizontal algebra structures do not appear in the theorem's
type. This permits later application to a field automorphism without replacing
the vertical scalar structures. No conjugated zero datum or full Galois
stability assertion is claimed here.
