# Actual subgroup multiplication as an equivariant semidirect factorization

This internal construction works over any scheme `B` in universe `u`.
It takes group-scheme maps `i : N ⟶ P` and `j : K ⟶ P`, an actual
`K`-action `a` on `N`, and its conjugation equation after composition
with `i`, on every scheme over `B`.

`semidirectFactorPoints` uses the ordinary semidirect-product universal
homomorphism on each test. Its value is the image of the normal coordinate
times the image of the acting coordinate. Naturality and group-valued Yoneda
produce `semidirectFactorHom`. The theorem `semidirectFactorHom_hom` identifies
its underlying scheme morphism with exactly `subgroupMultiplication i j`.
If this original multiplication map is an isomorphism of schemes over `B`,
`semidirectFactorIso` recovers the corresponding group-scheme isomorphism.
No existence of such a multiplication isomorphism is asserted.

For an external acting group `L`, suppose actions `b` on `P` and `c` on `N`
intertwine through `i`, while every point in the image of `j` is fixed by
`b`. If the underlying map of `i` is a monomorphism, cancellation and the
conjugation equation show that `c` commutes with `a`. The final theorem
shows that the constructed factor homomorphism intertwines the resulting
`semidirectLift` with `b`. All equations quantify over arbitrary test schemes,
including nonreduced tests; geometric-point bijectivity is not used.

The provenance is internal: the construction combines the published actual
semidirect group scheme, the semidirect-product universal homomorphism,
`homOfPoints`, the actual two-subgroup multiplication, and reflection of
isomorphisms by the group-object forgetful functors. It supplies the adapter
needed to transfer exact semigroup products from a compatible decomposition.
It proves neither the existence of a torus/unipotent decomposition nor scalar
descent or the full ordered-product proposition.
