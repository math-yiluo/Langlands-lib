# Proof of `Langlands.GroupScheme.RelativeRoot.RootProductStatement`

This module proves the published proposition `Langlands.GroupScheme.RelativeRoot.RootProductStatement` (module `Langlands.GroupScheme.Rational.RootProductStatement`) at every universe `u`. The statement is the conjunction of the three statements `SemigroupOrderedProductStatement`, `RelativeRootRayDecompositionStatement` and `DynamicRootOrderedProductStatement` of namespace `RelativeRoot`.

The theorem is `Langlands.GroupScheme.RelativeRoot.rootProduct : RootProductStatement.{u}`, with no hypotheses.

## Proof

The proof term is the anonymous constructor applied to the published proofs of the three conjuncts.

The theorem adds no mathematics; it names a combination of published results.

## Published inputs

- `Langlands.GroupScheme.RelativeRoot.semigroupOrderedProduct` (module `Langlands.GroupScheme.Rational.SemigroupOrderedProductProof`)
- `Langlands.GroupScheme.RelativeRoot.relativeRootRayDecomposition` (module `Langlands.GroupScheme.Rational.RootRayDecompositionProof`)
- `Langlands.GroupScheme.RelativeRoot.dynamicRootOrderedProduct` (module `Langlands.GroupScheme.Rational.DynamicRootOrderedProductProof`)
