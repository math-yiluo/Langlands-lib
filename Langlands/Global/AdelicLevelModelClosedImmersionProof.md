# Closed embeddings on actual arithmetic-level model points

Author: Worker 208.

`adelicLevelModelClosedImmersion` proves exactly
`AdelicLevelModelClosedImmersionStatement` in its original universe.
Both arithmetic clauses retain the original scheme models, scalar actions,
coefficient rings and point topologies, including all infinite number-field
factors. Neither affineness nor separatedness is assumed. The curve clause
allows arbitrary constants and empty finite sets.

The proof first base changes the given closed immersion to every actual local
factor. Stability of closed immersions under pullback and
`isClosedEmbedding_schemeClosedPointMap` show that postcomposition is a closed
embedding on the resulting local point spaces. Actual completed fields and
completed valuation rings are Hausdorff local topological rings, and
`adelicLocalFactorUnits` supplies their open-unit hypothesis. The product of
these local closed embeddings is a closed embedding.

The source structure morphism is finite type because it is the composition of
the closed immersion with the finite-type target structure morphism. Thus
`curvePlaceLevelModelPointMap_isHomeomorph_of_finiteType` and
`numberFieldLevelModelPointMap_isHomeomorph_of_finiteType` identify both original
arithmetic-level point spaces with the relevant products. Naturality of
coefficient restriction and actual scheme base change gives the commutative
square with postcomposition. Composing the product closed embedding with the
source comparison and cancelling the target embedding proves the assertion for
the original arithmetic-level map.

This implements the local-product step used on printed p.9 of Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Corollary 3.7 and the beginning of Section 4. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Passage to the full final adelic topology is a separate obligation.
