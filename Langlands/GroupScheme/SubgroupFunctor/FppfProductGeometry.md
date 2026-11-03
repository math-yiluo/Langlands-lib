# Multiplication onto represented fppf products

This module supplies the multiplication map and image properties for an existing
represented fppf-local product. It works over an arbitrary scheme
`S : Scheme.{u}`, with no restriction on the universe. Its namespace is
`Langlands.GroupScheme.SubgroupFunctor.IsFppfProduct`.

## Provenance and scope

This is internal derived geometry for the pseudo-parabolic structure proof.
The hypotheses are the published `IsFppfProduct F N i` and representations
`hH : F.IsRepresentedBy j`, `hU : N.IsRepresentedBy l`, where
`j : H ⟶ G`, `l : U ⟶ G`, and `i : P ⟶ G` are actual group-scheme
homomorphisms. The results follow directly from the all-test local lifting
condition in `SubgroupFunctor.FppfProduct` and from Mathlib's theorem that a
flat surjective scheme morphism is an epimorphism. The connectedness application
also uses the Library's geometric connectedness theorem for connected finite
type group schemes over a field. No new result from external literature is
asserted here.

The module assumes that the factors and their fppf product have the supplied
representatives. It proves no representability or existence theorem. The
multiplication map is a morphism of schemes over `S`; no group homomorphism
property or flatness of that morphism is claimed.

## Construction

`productMul hi hH hU : H.X ⊗ U.X ⟶ P.X` is obtained as follows. On the
relative test scheme `H.X ⊗ U.X`, the two projections composed with `j` and
`l` are points of `F` and `N`. Their product is locally in the product by the
identity cover. The equivalence in `hi.mem_range_iff` gives a lift to `P`.
Classical choice selects this lift. The theorem `productMul_comp` records its
composite with `i` as precisely the ordered ambient multiplication of the two
universal points.

## Image properties

`exists_cover_productMul` applies `hi.mem_range_iff` to the universal point
`i : P.X ⟶ G.X`. It obtains a flat surjective locally finitely presented
relative map `v : V ⟶ P.X` with a factorization of the pullback point into
`F` and `N`. The representation equalities lift these two points to `H` and
`U`. Their product pairing is `r : V ⟶ H.X ⊗ U.X`. Composing with `i`
and using `productMul_comp` proves `r ≫ productMul hi hH hU = v`;
closedness of `i` supplies the monomorphism needed to cancel it.

`epi_productMul` applies `Flat.epi_of_flat_of_surjective` to `v.left`.
Since `v.left` factors through `(productMul hi hH hU).left`, the latter is
an epimorphism of schemes. `surjective_productMul` uses the same factorization
to obtain surjectivity on underlying scheme points. These results do not
assert surjectivity on the group of points over each original test scheme.

## Connectedness

`connectedSpace_of_product` descends connectedness from
`(H.X ⊗ U.X).left` to `P.X.left` using the continuous surjective
multiplication map.

`connectedSpace` specializes this to a field and smooth connected affine group
schemes `H` and `U`. The published
`GroupScheme.geometricallyConnected_of_connected` makes `U` geometrically
connected; its smoothness makes its structure morphism universally open.
The corresponding pullback over the connected scheme `H` is connected by
Mathlib's geometric-connectedness pullback instance. The preceding descent
then makes `P` connected. Smoothness and affineness of `P` are separate
obligations.
