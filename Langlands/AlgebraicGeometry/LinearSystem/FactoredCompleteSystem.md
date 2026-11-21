# Section pullback for a factorization of a complete linear system

Let `C` be a complete generating system of a line bundle `N` on a scheme `X`
over a field `K`. Suppose its actual map to projective space factors as
`X → B → P`, with the first map `q` over `K` and the second map denoted `g`.
`factoredTwistIso` compares `q^* g^* 𝒪(1)` with `N`. It composes the
pullback composition and equality comparisons with the actual linear-system
twist isomorphism. `factoredTwistIso_coordinate` carries the iterated
pullback of each projective coordinate section to the corresponding member
of `C.basis`.

In `surjective_pullback_of_factorization`, the pullback map on relative
(global `K`-linear) sections of `g^* 𝒪(1)` is surjective. After the twist
comparison, its image contains each member of the complete basis by using
the `g`-pullback of the corresponding coordinate section as a preimage.
The range is a linear subspace, so containing the basis makes it the whole
space. No flatness or surjectivity assumption on `q` is needed for this
direction. If `q` is flat and surjective, the Library's section-pullback
injectivity theorem also applies. `factoredSectionsEquiv` is then the
`K`-linear equivalence given by actual pullback from `g^* 𝒪(1)` to its
`q`-pullback. In particular the two relative section spaces have the same
finite rank when finite dimensional.

This is an internal adapter, composing the Library's coordinate, module
pullback and flat section detection interfaces. Its use in cubic separation
is to compare dimension of sections on a supplied quotient with dimension on
the original abelian scheme. It neither constructs the quotient nor asserts
ampleness of the descended twist or that `q` is an isomorphism.
