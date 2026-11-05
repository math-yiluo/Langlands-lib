# Semigroup intersection with a connected solvable subgroup

Worker 1345. This is a derived application of the published semigroup
intersection consumers and their now proved geometric prerequisites.

`SemigroupSolvableIntersectionStatement.{u}` isolates the solvable alternative
of the existing `SemigroupIntersectionStatement.{u}`, with its original
hypotheses and quantifiers. `semigroupSolvableIntersection` proves this focused
proposition by introducing its data and applying the theorem below.

`Langlands.GroupScheme.RelativeRoot.semigroup_comap_eq_of_connected_solvable` proves
the solvable alternative of semigroup intersection comparison at every universe
`u`. Let `k : Type u` be any field, let a split torus `S` act on smooth affine
group schemes `G` and `H`, and suppose `H` is connected and satisfies
`IsSolvableScheme H`, the uniform all-test solvability condition. For an
equivariant closed subgroup homomorphism `j : H ⟶ G` and every additive
subsemigroup `A` of the character lattice, it proves

```text
(semigroupSubgroup b A).comap j = semigroupSubgroup c A.
```

This is equality of the actual subgroup functors on every scheme test. Zero is
allowed in `A`. The theorem retains the given smoothness, affineness,
connectedness, split-torus, equivariance and solvability hypotheses.

The proof splits according to membership of zero in `A`.

- If zero belongs, it applies
  `semigroup_comap_eq_of_solvable_of_zero_mem` from
  `Rational.SemigroupSolvableIntersection`. The published
  `Torus.solvableFixedContainmentConnected` supplies the general connectedness
  criterion and `RelativeRoot.semigroupRealization` supplies realization.
  The consumer puts the full torus fixed subgroup in the semigroup subgroup,
  makes the smooth closed intersection representative connected, and concludes
  equality using its exact Lie image.
- If zero does not belong, it applies
  `semigroup_comap_eq_of_zero_not_mem` from
  `Rational.SemigroupZeroExcludedIntersection`, supplying the same realization
  theorem and `CoordinateWeights.coordinateSemigroupComparison.2`, the proved
  augmentation Lie containment statement.

All geometric proposition premises of these consumers are discharged by the
imported published theorems. This module proves the full solvable alternative;
the normal alternative and the full comparison conjunction are separate.
