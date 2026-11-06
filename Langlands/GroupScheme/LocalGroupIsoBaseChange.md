# Local group isomorphisms from base change

This internal construction relates an actual isomorphism of group schemes after
base change to the natural local isomorphisms used in
`Langlands.GroupScheme.LocalGroupIso`. It is derived from the pullback
adjunction and the existing multiplicative `baseChangePointsEquiv`; no
structural existence theorem is assumed or proved.

For every scheme `T` over `S` and every cover point `a : T ⟶ U`, `coverTest a`
is the same underlying scheme over `U`. The comparison `coverTestIso a`
identifies its image over `S` with `T`. The multiplicative equivalence
`coverPointsEquiv` projects points of the actual pullback group scheme to
points of the original group scheme. Its projection formula and its
naturality, in both directions, are proved for every relative test scheme.

`ofBaseChangeIso` lifts a point of `G` using this equivalence, applies the
given base-change isomorphism, and projects to `H`. Composition of the three
multiplicative equivalences proves multiplicativity and bijectivity.
Naturality follows from the two projection equivalences and associativity of
composition. `ofBaseChangeIso_toFun_left` records the underlying scheme
morphism formula.

The construction works in arbitrary universe `u`, for every base scheme,
every object `U` over it, and arbitrary group schemes. It needs no covering
property of `U`. In particular, it does not construct a quasi-split model,
an adjoint quotient, a finite Galois extension, or a discrepancy cocycle.
