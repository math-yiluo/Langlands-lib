# Equivariant maps of semidirect group schemes

This internal construction works over an arbitrary base scheme in any universe.
Let a group scheme `K` act by actual automorphic actions `c` on `H` and `a` on
`G`. Let `f : H ⟶ G` be a group scheme homomorphism which intertwines those
actions on every test scheme.

`semidirectMapPoints` applies `f` to the normal coordinate and the identity to
the acting coordinate. Equivariance makes this a homomorphism of the actual
semidirect point groups; associativity of composition makes it natural in
the test scheme.

`semidirectMap` recovers the corresponding group scheme homomorphism using the
fully faithful group valued Yoneda functor and the existing semidirect point
isomorphisms. `semidirectMap_points` proves its stated formula on every test.
`semidirectMap_hom` identifies its underlying scheme morphism with
`f.hom.hom ⊗ₘ 𝟙 K.X`. This construction uses no smoothness, affineness or
connectedness assumptions.

The provenance is internal: the proof combines Mathlib's semidirect group
homomorphism with the Library's actual semidirect group scheme representation.
It is intended for absorption of a normalizing group into a chosen factor of
an ordered group scheme product. It does not prove any semigroup realization,
solvable decomposition or scalar descent statement.
