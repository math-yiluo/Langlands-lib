# Affine quotients by normal closed subgroups

Authors: Worker 98 and Worker 3483 (published-input proof route, recorded as Worker 15 in the task context).

`Langlands.GroupScheme.affineNormalSubgroupQuotient.{u}` proves exactly
`Langlands.GroupScheme.AffineNormalSubgroupQuotientStatement.{u}`. Its type has no added hypotheses or proposition-valued parameters.

Over every field, every normal closed subgroup of an affine locally finite-type group admits an affine locally finite-type quotient with the exact all-test scheme-kernel equality and an fppf projection. The published formulation uses typeclass hypotheses for the source geometry and puts local finite type before affineness in the quotient conclusion. It permits nonreduced groups without a smoothness or connectedness assumption.

The implemented proof uses these published theorems:

- `Langlands.GroupScheme.NormalSubgroupQuotientExistenceStatement.toAffineNormalSubgroupQuotientStatement` from
  `Langlands.GroupScheme.AffineNormalSubgroupQuotientEquivalence`.
- `Langlands.GroupScheme.normalSubgroupQuotientExistence` from
  `Langlands.GroupScheme.NormalQuotientExistenceProof`.

The published conversion applies the unconditional normal-subgroup quotient existence theorem, supplies the source geometric instances as explicit arguments, and reorders the two geometric conclusions. It retains the actual quotient, projection and complete `RelativeRoot.IsFppfQuotient` witness.

The complete proof term is:

```lean
NormalSubgroupQuotientExistenceStatement.toAffineNormalSubgroupQuotientStatement
    normalSubgroupQuotientExistence
```

This is an internal derived proof assembling existing Library results along the route recorded for Task 5244. The target statement and its imports are unchanged.
