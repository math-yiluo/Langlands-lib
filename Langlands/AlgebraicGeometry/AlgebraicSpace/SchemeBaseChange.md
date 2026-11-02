# Scheme representation under restriction to a base scheme

This internal construction uses the ordinary adjunction
`Over.map g ⊣ Over.pullback g` and the lifted scheme Yoneda presheaves.
For any scheme morphism `g : T → S` and any scheme `G` over `S`,
`schemeYonedaBaseChangeIso g G` identifies the full functor of points of
the actual base change `G ×ₛ T` over `T` with the restriction of the
functor of points of `G` along `Over.map g`.

At each `Z : Over T`, the component is the lifted inverse of the
adjunction's Hom equivalence. Its naturality is the adjunction identity
`homEquiv_naturality_left_symm`, which compares restriction along every
scheme morphism over `T`.

`representedBaseChangeIso g G e` composes this isomorphism with the
restriction of any given full natural scheme representation `e`.
It applies to all schemes and all presheaves in the published
`AlgebraicSpace.Presheaf` universe convention. No topology, finiteness,
reducedness or compactness hypothesis enters the construction, and no
representation existence theorem is asserted.
