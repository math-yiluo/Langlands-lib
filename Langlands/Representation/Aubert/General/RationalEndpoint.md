# The rational full-index and empty-root identities

This internal endpoint specialization keeps the actual rational-point standard subgroups, the literal simple relative-root labels, and the canonical evaluation topology used by `rationalAlternatingOperator`. It is derived from the published structural comparison premise `StandardCocharacterStatement` and the normalized-functor endpoint comparison in `Langlands.Representation.Aubert.General.Endpoint`; it introduces no new endpoint or functor-identity premise.

The zero cocharacter is standard at the full simple-root set by `isStandardCocharacter_simple_zero`. Applying the supplied standard-cocharacter comparison to that cocharacter, then using `groupHom_zero_comp_eq_trivialCocharacter` and the dynamic trivial-cocharacter identities, gives the whole-group parabolic and Levi. `standardUnipotent_simple_eq_bot` gives the trivial radical. Evaluating these subgroup functor equalities on the actual identity-test rational points and using `rootSet_univ` proves `parabolic_univ_eq_top`, `levi_univ_eq_top`, and `unipotent_univ_eq_bot`. No generic-centralizer premise is needed.

`fullIndexInductionJacquetIso` specializes `endpointInductionJacquetIso` to the actual full-index semidirect decomposition and the three proved subgroup equalities. It is an isomorphism from normalized induction after Jacquet restriction to the original smooth rational-point representation, on the original coefficient carrier of universe `max (u + 1) v`. It uses the supplied radical closedness at the full index and no finite-length premise.

`alternatingTerm_univ_eq_id` applies `endpoint_inductionK0_comp_jacquetK0` to these actual subgroup equalities. Its endomorphism is literally the full-index `alternatingTerm` on the exact finite-length Grothendieck group. The closedness, continuous projection, compact-limit radical, and separate induction/Jacquet finite-length premises retain the scopes used by `standardParabolicFiniteLength`. The equality holds on the entire group with all short exact sequence relations, including nonsplit ones. The group and coefficient universes remain independent; the rational operator uses the original carriers of universe `max (u + 1) v`.

If the simple-root type is empty, `rationalAlternatingOperator_of_isEmpty` reduces the same actual operator to its empty-index term. That index is also the full index, so the endpoint identity proves `rationalAlternatingOperator_eq_id_of_isEmpty`. Rewriting by this equality proves `rationalAlternatingOperator_sq_eq_id_of_isEmpty`. These results do not prove involutivity when simple roots are present.

The route uses no Langlands classification, character independence, geometric lemma, adjointness, cuspidal-support theorem, or Aubert Proposition 3.2. Its prerequisites are the displayed structural comparison and the actual normalized constructions and exact-K0 formulas, with the elementary endpoint argument implemented in the imported endpoint module.

The local topology instance is named `rationalEndpointPointTopology` to avoid
generated-name collisions when rational-family modules are imported together.
Its defining value remains `pointTopology`.
