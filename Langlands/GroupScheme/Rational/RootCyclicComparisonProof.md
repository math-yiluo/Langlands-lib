# Cyclic comparison for actual relative roots

Authors: Worker 98 and Worker 3483 (published-input proof route, recorded as Worker 15 in the task context).

`Langlands.GroupScheme.RelativeRoot.actualRootCyclicComparison.{u}` proves exactly
`Langlands.GroupScheme.RelativeRoot.ActualRootCyclicComparisonStatement.{u}`. Its type has no added hypotheses or proposition-valued parameters.

Over every field, for a connected reductive group, a maximal split torus and an actual relative root, the first positive cyclic filtration term equals the actual relative-root subgroup functor. Equality is on every test scheme, and positive integral multiples retain the published nonreduced-root-system scope.

The implemented proof uses these published theorems:

- `Langlands.GroupScheme.RelativeRoot.actualRootCyclicComparison_of_realization_uniqueness` from
  `Langlands.GroupScheme.Rational.RootCyclicComparisonReduction`.
- `Langlands.GroupScheme.RelativeRoot.semigroupRealization` from
  `Langlands.GroupScheme.Rational.SemigroupRealizationProof`.
- `Langlands.GroupScheme.RelativeRoot.rootSubgroupUniqueness` from
  `Langlands.GroupScheme.Rational.RootSubgroupUniquenessProof`.

Semigroup realization supplies a smooth connected closed representative with stability and the specified Lie image. The reduction identifies that Lie image with the positive weight span and applies actual-root uniqueness. The published uniqueness proof uses the broader published cyclic comparison; it does not import this new proof.

The complete proof term is:

```lean
actualRootCyclicComparison_of_realization_uniqueness
    semigroupRealization rootSubgroupUniqueness
```

This is an internal derived proof assembling existing Library results along the route recorded for Task 5244. The target statement and its imports are unchanged.
