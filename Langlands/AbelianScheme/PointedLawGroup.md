# Pointed group laws on the pullbacks of a family

Let `X` and `T` be objects of `Over S`. A `PointedLaw.Law X T` consists of a
map `(X ×ₛ X) ×ₛ T ⟶ X` for multiplication and a map `X ×ₛ T ⟶ X` for
inversion. A section of `X ⟶ S` specifies the unit. The operation maps can
be evaluated on any generalized points of `X` with a common parameter in
`T`. `Law.IsGroup` requires associativity, commutativity, the left unit
identity and the left inverse identity on these generalized points. The
restriction of a candidate law uses precomposition in the parameter.

## Actual pullback and geometry

The adjunction `Over.map ⊣ Over.pullback` turns maps `P ×ₛ T ⟶ X`
over `S` into maps `P ×ₛ T ⟶ X ×ₛ T` over `T`. The binary product
comparison for the pullback functor gives the multiplication map in
`Over T`. The same adjunction transports the unit and the inverse. The
proof computes how these maps act on points and compares the pointwise
equations in the two slices. The equations produce an internal group
object. Commutativity supplies the right unit and right inverse identities.
Conversely, the pointwise laws of a commutative group object with the
prescribed unit give `Law.IsGroup`.

For a smooth proper family with geometrically connected fibres, `Law.unique`
applies `pointedMorphismRigidity` to the identity map between the same
pullback endowed with two such group objects. The identity preserves the
unit. Smoothness gives local finite presentation of the pullback and
properness gives quasi-compactness and quasi-separatedness. The identity
therefore preserves multiplication and inverse, which determines both
parameterized operations by the adjunction.

`exists_law_iff` compares the existence of a law with
`HasPointedAbelianPullback`. A law on the pullback supplies the required
abelian-scheme bundle by stability of smoothness of relative dimension,
properness and geometric connectedness under base change. Conversely, the
isomorphism over the test scheme in `HasPointedAbelianPullback` transports
the given abelian-scheme group law to the pullback. The identity agrees with
the pulled-back section by the two pullback projections.

The equations implement the group-law description used in Mumford, Fogarty
and Kirwan, *Geometric Invariant Theory*, 3rd ed. (1994), Proposition 6.16,
printed pp. 126–127 (PDF pp. 139–140). The uniqueness argument implements
Corollary 6.6, printed p. 117 (PDF p. 130), using the Library's
arbitrary-base rigidity theorem.
