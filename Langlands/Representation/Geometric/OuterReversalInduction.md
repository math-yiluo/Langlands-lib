# Actual refined induction under outer reversal

This is an internal construction derived from `Geometric.OuterReversal`,
`Geometric.FlattenedLevi`, the actual refined normalized-induction definitions,
and `Induction.SmoothGroupTransport`. It supplies a representation-level
comparison for the Jacquet compatibility proof.

For an ordered positive block shape `B` and refinement `S`, set
`S' = outerReverseRefinement B S`. The equivalence
`outerReverseFlattenedLeviEquiv` sends the actual product Levi of `B.flatten S`
to that of `B.reverse.flatten S'`. Its definition passes through the two
published flattened-coordinate equivalences and the actual refined-subgroup
outer reindexing. The matrix identity
`reverseMatrix_conj_outerReverseFlattenedLeviEquiv` follows by the flattened
embedding formula and the coarse reversal conjugation identity. Thus
`conjugatesLevi_outerReverseFlattened` proves concrete conjugacy by
`B.reversePermutation`, sending the reversed flattened embedded Levi onto the
original one. No permutation involutivity is assumed.

The inverse-conjugation lemmas identify the actual inverse Levi conjugations,
for any proof of these concrete conjugacy propositions, with the constructed
coarse and flattened outer reindexings. The proof uses injectivity of the actual
Levi embeddings and cancels the conjugating matrices. The continuous coarse
identity packages the same calculation with the actual product topologies.
`outerReverseFlattenedLeviEquivContinuous` similarly packages the flattened map.

For any prime, supplied p-adic field `F`, topology `T`, and complex representation
`σ` of the reversed refined Levi, `refinedInducing_outerReverse` proves equality
of the two actual inducing actions. The equality uses the actual diagonal
projection identity and the equality of the positive half-modulus characters;
it retains the upper-parabolic covariance convention.

`normalizedRefinedInduced_outerReverseEquiv` is an actual representation
equivalence from reversed normalized refined induction, pulled back to `B.Levi`
along outer reindexing, to normalized refined induction of the reindexed
inducing action. It applies the generic smooth-induction precomposition
construction to the actual coarse topological group equivalence and its refined
parabolic restriction. Hence it acts by precomposition on actual covariant
smooth induced functions and intertwines right translation.

The constructions allow arbitrary rank, including zero, independent field and
representation-carrier universes, and arbitrary inducing representations. They
impose no finite length, admissibility, irreducibility, or dimension hypothesis.
They do not yet assert the K0 comparison or final Aubert compatibility.
