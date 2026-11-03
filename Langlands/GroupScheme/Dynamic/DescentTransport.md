# Dynamic parabolics under canonical descent transport

Worker 1270. This is an internal consequence of the published constructions in
`CocharacterTransport`, `Dynamic.BaseChange`, and `Dynamic.Functoriality`.
It supplies an all-test-scheme comparison needed for cocharacter descent in the
parabolic classification. Its proofs use those constructions directly, with no
additional assertion from the literature.

Let `b : S → B` and `a : S → S` be scheme morphisms satisfying `a ≫ b = b`.
Let `G` be an arbitrary group scheme over `B`. The map `a` need not be invertible.
The canonical `descentBaseChangeIso` identifies `a*(b*G)` with `b*G`.

The definition `SubgroupFunctor.descentTransport` sends a subgroup functor `H`
of `b*G` to the preimage of `H.baseChange a` under the inverse descent
identification. This is an actual subgroup functor on every test scheme;
`mem_descentTransport` gives its membership condition using the pullback point
equivalence.

The theorem `SubgroupFunctor.baseChange_descent_comap` states that for every
subgroup functor `F` of `G`, pulling `F` back along `b` and then `a`, and taking
its preimage under the inverse descent identification, gives exactly `F` pulled
back along `b`. The proof uses `baseChangePointsEquiv_descent` to identify the
corresponding points over `B`. The two test schemes over `B` are identified by
`descentTestIso`; functoriality of `F` along that isomorphism and its inverse
proves the membership equivalence. The theorem `descentTransport_baseChange`
expresses the same result as invariance under the defined transport.

For a cocharacter `χ : Gm_S → b*G`,
`Dynamic.parabolic_transportCocharacter` identifies the parabolic of
`transportCocharacter b a ha G χ` with the preimage of `(P(χ)).baseChange a`
under the inverse descent isomorphism. The proof cancels the descent
isomorphism after transport, then uses the existing functoriality under a group
isomorphism and compatibility of dynamic parabolics with base change. The
alias `parabolic_transportCocharacter_eq_descentTransport` expresses this
comparison using the subgroup-functor transport definition.

Finally `Dynamic.parabolic_transportCocharacter_eq_baseChange` shows that if
`P(χ) = F.baseChange b`, then every transported cocharacter has the same
parabolic `F.baseChange b`. Equality holds on every scheme over `S`.
No affineness, representability, finiteness, smoothness, field, torus, or
reductivity hypothesis is used. This result does not construct the initial
cocharacter or prove parabolic classification.
