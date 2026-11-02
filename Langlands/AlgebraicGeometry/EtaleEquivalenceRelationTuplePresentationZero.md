# The original relation as the zero component of the finite tuple family

This is derived infrastructure for the symmetric tuple construction in
Stacks Project, Lemma 68.8.3 (Tag 0BBN), and its finite version in Lemma
68.8.6 (Tag 07ST). The registered originals are
`stacks-stratification-2026-11-02` and
`stacks-noetherian-approximation-2026-11-01`. A tuple parameter `n` means
`n+1` entries. Consequently the zero chart represents the original objects,
and the zero-zero cross-correspondence represents the original arrows.

The module assumes separated source, affine object and relation schemes,
and a closed joint endpoint map, in arbitrary scheme universe `u`.
It uses the actual scheme isomorphisms already constructed in
`EtaleEquivalenceRelationTupleZero`. The inverse endpoint identities
`tupleSymmetricCrossZeroIso_inv_t` and
`tupleSymmetricCrossZeroIso_inv_s` follow by composing the established
forward endpoint identities with the two inverses.

`tupleZeroSingletonObjectIso` and `tupleZeroSingletonRelationIso` identify
the original schemes with the singleton coproduct presentations.
The singleton coproduct isomorphisms follow the inverse one-entry tuple
isomorphisms. Their endpoint identities follow from the component endpoint
formulas and the inverse endpoint identities above.

`tupleFiniteZeroObjectMap N` and `tupleFiniteZeroRelationMap N` include
the original schemes in the zero and zero-zero components of the finite
tuple presentation through length `N`. Both are open and closed immersions:
the singleton reindex formulas express them as an isomorphism followed by
an open and closed subfamily inclusion. Their
endpoint identities retain the original `t` and `s` maps. The two
`tupleZeroSingleton..._reindex` formulas identify them with the singleton
isomorphisms followed by reindexing into the full family.

`tupleFiniteZero_isPullback_pair` states that the original relation is the
pullback of the finite presentation along both original object endpoints.
The proof first uses the singleton isomorphisms to form an isomorphic
pullback square, then pastes it with the established singleton-subfamily
pullback. This preserves the scheme structure on arbitrary test schemes.

`tupleFiniteZeroChartMap` lifts each original arrow to the actual
`Chart.arrows` of the finite tuple presentation along
`tupleFiniteZeroObjectMap`. Its three equations identify both endpoints
and its map to the full relation scheme. `tupleFiniteZeroChartIso`
identifies the original relation scheme with this actual chart relation
by uniqueness of pullbacks. Its forward-morphism identity is proved by
checking the two chart endpoints.

The comparison is along both endpoints. It supplies an actual chart
identification and does not assert source cartesianness or the existence
of a Noetherian first level.
