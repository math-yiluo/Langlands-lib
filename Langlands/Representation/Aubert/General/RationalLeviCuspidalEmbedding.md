# Cuspidal embeddings inside an actual standard rational-point Levi

This internal supporting construction combines the published
`exists_nonzero_cuspidal_leviJacquet` theorem with the generic quotient and
adjointness argument in `CuspidalQuotientEmbedding`. It continues Worker 379's
minimal-Jacquet approach on the actual rational-point Levi, keeping the actual
root labels and the literal subgroup quotients.

`isUnimodularModulus_standardUnipotent_in_levi` proves unimodularity of each
restricted standard radical. The standard cocharacter statement gives its
ambient compact-subgroup-limit property. Restriction to a closed Levi preserves
that property, which implies unimodularity.

`exists_cuspidal_embedding_in_levi` starts with an irreducible smooth
representation of a standard Levi. The published minimal-index theorem provides
a nonzero cuspidal normalized Jacquet module on a smaller actual standard Levi.
The generic irreducible-quotient construction, using compactness of the literal
inside-Levi parabolic quotient, supplies an irreducible quotient and an actual
embedding into normalized induction from it. The exposed surjective morphism
transfers cuspidality by `IsLeviCuspidal.of_surjective`. The functors are exactly
`leviNormalizedJacquetFunctor` and `leviNormalizedInductionFunctor`, including
the continuous identifications of subgroup copies.

The theorem retains the standard cocharacter and Levi intersection statements,
the local-field and ambient topological assumptions, closedness of all standard
Levis and radicals, and compactness of every literal inside-Levi parabolic
quotient. The representation carrier has size `max u v`, matching the induction
functor. No admissibility or finite-length premise is introduced. This is an
intermediate theorem: the final full support-category vanishing target must
discharge quotient compactness from its own premises.
