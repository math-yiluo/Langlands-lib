# The étale equivalence relation of a local presheaf representer

This internal construction starts with schemes `S,U` in universe `u`, an étale
morphism `p : U → S`, and a representation `e` of the restriction of a
`Type v` valued presheaf `F` by a scheme `M` over `U`. The universes remain
independent. No sheaf, surjectivity, properness or polarization is assumed.

`LocalRepresenter.etaleRelation` has chart `M` and relation scheme
`M ×_S U`. Its projections are the first pullback projection and the local
classifier constructed in `LocalRepresenterOverlap`. The matching-pair and
uniqueness results in `LocalRepresenterRelation` supply its relation laws on
every scheme-valued test point. Reflexivity lifts a chart map paired with
itself. Symmetry uses the exchange isomorphism. For transitivity, the equality
of the middle chart maps puts both relation points over the same `S`-scheme;
transitivity of equality of their classified families then supplies a matching
pair. The raw scheme projection uniqueness proves the product map is monic.

The first projection is a base change of `p`, hence étale. The exchange
isomorphism identifies the second projection with the first after an
isomorphism, so it too is étale. This construction establishes an actual
`EtaleEquivalenceRelation`; it does not assert effectivity or a scheme quotient.
