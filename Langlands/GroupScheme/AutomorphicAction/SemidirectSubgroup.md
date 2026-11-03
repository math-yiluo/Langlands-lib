# Stable subgroup functors inside a semidirect product

This internal construction works over an arbitrary scheme and universe.
An actual action `a` of `K` on `G` and an all-test subgroup functor `F` of `G`
are given, together with stability of `F` under `a`.
`semidirectSubgroup` is the all-test subgroup of `a.semidirectProduct`
whose normal coordinate belongs to `F`. Multiplication and inversion preserve
membership by stability; precomposition preserves it by naturality.

Every semidirect point factors as its normal coordinate inclusion times its
acting coordinate inclusion. Thus the extended functor restricts to exactly
`F` on the normal factor, contains the entire acting factor, and is the
smallest subgroup functor containing these two images. It is monotone in `F`.
These assertions concern all tests, including nonreduced tests.

For an actual equivariant homomorphism of normal factors, the exact range
of its induced semidirect map consists of points whose normal coordinate
is in the original range. One direction reads coordinates; the other lifts
an original range witness together with the unchanged acting coordinate.
Coordinate cancellation proves that a monic original map gives a monic
semidirect map. The underlying semidirect map is the product of the original
map and the identity, so a closed original inclusion gives a closed
semidirect inclusion by stability of closed immersions under products.

When `F` is represented by an actual inclusion, its induced restricted action
and semidirect map construct `semidirectSubgroupInclusion`, representing
the extended functor. Closedness passes from the original representative.
Finally, stability of `F` under another actual action commuting with `a`
implies stability of the extension under its constructed semidirect lift.

The provenance is internal, using the existing semidirect coordinates,
equivariant semidirect maps, represented subgroup actions, and product
closedness. This unit makes no smoothness, connectedness, field or torus
assumption. It does not identify these extended functors with semigroup
subgroups or prove existence of a solvable decomposition or scalar descent.
