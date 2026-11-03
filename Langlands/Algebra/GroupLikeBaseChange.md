# Scalar extension of a coalgebra spanned by group-like elements

This internal helper is derived from Mathlib's linear independence theorem for
group-like elements and the scalar extension of a basis. It supports the lattice
identification in finite Galois splitting of actual field tori. It does not
assert that the coordinate coalgebra of an arbitrary torus is spanned by its
group-like elements; that remains a separate separable-closure argument.

For any extension of fields K/k and any k-coalgebra C, the canonical map
`Langlands.GroupLike.baseChange` sends g to 1 ⊗ g. The tensor product coalgebra
formulas show that the image is group-like. The three types may have different
universes.

If the group-like elements span C, their known linear independence makes them
a basis, `basisOfSpan`. Its scalar extension is a K-basis of K ⊗ C consisting
of the same pure tensors. Hence the canonical map is injective and its image
spans. Any group-like element outside that image, together with the image,
would be linearly independent by Mathlib's independence theorem, contradicting
the spanning property. This proves `baseChange_bijective` and constructs
`baseChangeEquivOfSpan`.

The proof uses the coalgebra structure alone. No finite dimensionality,
separability or algebraic restriction on the field extension is imposed.

For a k-bialgebra whose underlying algebra is a ring,
`baseChangeMonoidHom` packages the same map as a monoid homomorphism: pure
tensors with one preserve the unit and multiplication.
`baseChangeMulEquivOfSpan` combines this homomorphism with the preceding
bijectivity theorem. Its value on g is still 1 ⊗ g, as recorded by
`baseChangeMulEquivOfSpan_apply`. In particular, for a Hopf algebra this
identifies the groups of group-like elements as multiplicative groups.

The underlying independence result is Mathlib's
`linearIndep_groupLikeVal` and its set-indexed version
`linearIndepOn_isGroupLikeElem`. The basis extension uses
`Module.Basis.baseChange`. These internal constructions and their proofs
make no claim to be a separately stated result in the original torus
literature.
