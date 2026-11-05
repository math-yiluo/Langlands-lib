# Exact ordered semigroup products for solvable groups

Authors: Worker 1313 and Worker 362.

`Langlands.GroupScheme.RelativeRoot.semigroupOrderedProduct` proves exactly the
published proposition `SemigroupOrderedProductStatement.{u}` in
[`RootProductStatement`](RootProductStatement.md), for arbitrary universe `u`.
The target pair and all of its imports are unchanged.

For every field, every smooth connected affine solvable group scheme, every split
torus with its actual automorphic action, and every finite ordered partition of the
complete occurring Lie-weight support, the theorem supplies smooth connected closed
representatives of the generated semigroup functors. Their actual
`orderedMultiplication` morphism is an isomorphism of schemes over the original
field. The representation equalities retain every test scheme.

The hypotheses are the original disjointness of distinct blocks and exactly
`Disjoint (Ψ r) (AddSubsemigroup.closure (Ψ s))` for distinct indices. Generation
is positive additive semigroup generation, without adjoining zero. Zero is
included in the partition whenever it occurs as a weight. The statement covers
every indexed order and `Fin 0`; it imposes no disjointness condition on two
generated closures.

## Implemented proof

The proof applies
[`semigroupOrderedProduct_of_solvableStructuralInputs`](SolvableOrderedProductReduction.md)
and supplies all three of its structural premises from published theorems:

1. The maximal-torus semidirect statement follows by applying
   `solvableMaximalTorusSemidirectStatement_of_solvableTorusQuotient` in
   [`TriangularTorusConjugacy`](../Absolute/TriangularTorusConjugacy.md) to
   [`solvableTorusQuotient`](../Absolute/SolvableTorusQuotientProof.md) and
   [`solvableSplitExtension`](../Absolute/SolvableSplitExtensionProof.md).
   This uses the actual unipotent kernel and a homomorphic section of its
   represented fppf split-torus quotient. The published reduction handles the
   specified maximal torus and the actual multiplication isomorphism.
2. [`Torus.solvableFixedContainmentConnected`](../Torus/SolvableFixedContainmentConnectedProof.md)
   supplies the exact solvable fixed-containment connectedness statement.
3. [`centralStableVectorSubgroup`](CentralVectorQuotientProof.md) supplies
   central stable vector-subgroup existence.

The first reduction descends from algebraically closed fields to the original
field. Over an algebraically closed field it uses compatible actual factors: a
smooth connected unipotent normal factor and a torus fixed by the acting split
torus. The normal factor inherits solvability through its monomorphic inclusion.
The central-vector induction proves its ordered-product property; the
fixed-containment input supplies the needed semigroup inverse-image comparison.
The semidirect assembly and equivariant factor isomorphism transfer the result
to the ambient group, preserving the original ordered multiplication.

Every supplied theorem has its full universe-general statement and no additional
structural premise. Consequently this composition proves the exact arbitrary-field
target without adding hypotheses.

## Provenance

This module is a derived composition of the published reductions and proof
theorems named above. The central-vector induction and solvable ordered-product
reduction include joint work of Worker 1313 and Worker 362. Its mathematical
target is CGP, *Pseudo-reductive Groups*, second edition (2015), Theorem 3.3.11
and its proof, printed pp.114–116 (PDF pp.140–142), as documented in the unchanged
target Markdown. The stronger sufficient hypothesis of KP Theorem 2.11.15 is
not substituted for the exact CGP hypothesis.
