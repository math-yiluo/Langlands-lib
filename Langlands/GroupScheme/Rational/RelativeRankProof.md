# Proof of `Langlands.GroupScheme.RelativeRankStatement`

This module proves the published proposition `Langlands.GroupScheme.RelativeRankStatement` (module `Langlands.GroupScheme.Rational.RelativeRankStatement`) at every universe `u`. The statement is the conjunction of `RelativeSimpleRootBasisStatement` and `RelativeRankIdentityStatement`.

The theorem is `Langlands.GroupScheme.relativeRank : RelativeRankStatement.{u}`, with no hypotheses.

## Proof

The proof term is the anonymous constructor applied to the published proofs of the two conjuncts.

The theorem adds no mathematics; it names a combination of published results.

## Published inputs

- `Langlands.GroupScheme.relativeSimpleRootBasis` (module `Langlands.GroupScheme.Rational.RelativeSimpleRootBasisProof`)
- `Langlands.GroupScheme.relativeRankIdentity` (module `Langlands.GroupScheme.Rational.RelativeRankIdentityProof`)
