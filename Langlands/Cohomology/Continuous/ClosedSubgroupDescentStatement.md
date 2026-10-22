# Zero detection for restriction to a closed normal subgroup

Author: Worker 229.

`Langlands.Continuous.ClosedNormalRestrictionZeroDetection` is a
proposition (a `Prop`-valued definition). This module states it and does
not prove it.

## Exact statement

The proposition quantifies over the following data, all in one arbitrary
universe `u`:

- a commutative ring `k : Type u` with a topology;
- a group `G : Type u` that is a topological group (`IsTopologicalGroup`),
  compact (`CompactSpace`), Hausdorff (`T2Space`) and totally disconnected
  (`TotallyDisconnectedSpace`). In other words, `G` is a profinite group.
  `LocallyCompactSpace G` is not a separate hypothesis. Mathlib infers it
  from compactness and the Hausdorff property, so existing APIs that need
  it, such as the finite-quotient comparison, apply to `G`;
- a published `DiscreteModule k G` called `A`. This is a topological
  representation with the discrete topology whose action map
  `G × A → A` is jointly continuous;
- a closed subgroup `H : ClosedSubgroup G` (Mathlib's bundled closed
  subgroup) with `H.toSubgroup.Normal`. `H` is not assumed to be open, and
  it carries its actual subspace topology;
- a natural degree `q : ℕ`. Every degree is included, including `q = 0`;
- a class `x` in `continuousCohomology q A.toTopRep`, which is Mathlib's
  continuous cohomology, computed from continuous homogeneous cochains.

The hypothesis is that `continuousRestriction A H.toSubgroup q x = 0`.
Here `continuousRestriction` is the published map from
`Langlands.Cohomology.Continuous.FiniteQuotientSystem`. It is Mathlib's
`ContinuousCohomology.map` along `subgroupInclusion H`, the continuous
inclusion of `H` with its subspace topology, and uses the identity
coefficient morphism of `A.restrict H`, whose underlying representation is
`TopRep.res H.subtype A.toTopRep`. The map is applied to `x` through the
concrete-category coercion of `TopModuleCat`. This means applying its
underlying continuous linear map.

The conclusion is that some `N : OpenNormalSubgroup G` satisfies both
`H.toSubgroup ≤ N.toSubgroup` and
`continuousRestriction A N.toSubgroup q x = 0`. The restriction to `N` is
the same published map, taken along the inclusion of `N` with its subspace
topology.

The statement does not assume that `x` comes from a chosen finite
quotient. It adds no splitting, descent, vanishing or finite-stage
exactness hypothesis. It also asserts no colimit isomorphism, no converse
and no uniqueness of `N`.

## Provenance

This is an internal derived lemma about topological group cohomology. It
is not a verbatim theorem of the source. The source is Serre, *Local
Fields*, Greenberg translation (1979), registered as
`serre-1979-local-fields` at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Worker 229 read PDF pages 160–161 and 186–187. The project has no errata
note for this source.

- In X §3 (printed p.154 / PDF p.160), Serre takes a compact totally
  disconnected Galois group `G` and a module `A` that is the union of its
  invariants under open normal subgroups. He defines `H^q(G, A)` as the
  direct limit of `H^q(G/H, A^H)` over open normal subgroups, and notes
  that this cohomology can be computed with continuous cochains.
- XII §1, Theorem 1 (printed p.181 / PDF p.186) shows that a Brauer class
  which vanishes over the maximal unramified extension already vanishes
  over some finite unramified extension. The argument uses that the
  maximal unramified extension is a directed union of finite unramified
  extensions.

In Galois-cohomological terms, Theorem 1 says the following. If a class
vanishes after restriction to the closed normal inertia subgroup, it
vanishes after restriction to some open normal subgroup that contains
inertia. The proposition here abstracts that passage to an arbitrary
coefficient ring, an arbitrary profinite group, an arbitrary closed normal
subgroup and every degree. This generalization is the project's own
formulation.

The expected proof route is recorded for orientation only. It is not an
implemented proof. Since `G` is compact and `A` is discrete, continuous
cochains are locally constant. A cochain on `H` whose coboundary
represents the restriction of `x` should therefore factor through the
quotient of `H` by its intersection with a small open normal subgroup of
`G`, and so extend to the ambient group. The coboundary identity holds on
tuples from `H`. It should then hold on tuples from an open normal
subgroup that contains `H`, of the form `HN'` for a sufficiently small
open normal subgroup `N'` of `G`.

## Relation to other work

- The proof is a separate task. It will be published after this statement
  is accepted. The topological tuple-extension and neighborhood-agreement
  prerequisites are stated separately in task `1c8ea7cb`. This module does
  not import them.
- `FiniteStageExactnessLimit` in `FiniteStageExactnessLimitStatement` is
  distinct. It concerns an *open* normal subgroup and passes finite-stage
  inflation–restriction exactness to the continuous maps. The statement
  here involves no inflation or exactness. It concerns approximating a
  closed subgroup by open supergroups.
- `RestrictionMaps` and `SubgroupFiniteStages` treat restriction to open
  subgroups and finite-stage cofinality, which is the opposite direction
  of approximation.
- The intended consumer is the proof of
  `Langlands.ClassFieldTheory.Local.UnramifiedH2Exhaustion` (task
  `3263cf33`). There `G` is the absolute Galois group, `H` is the actual
  absolute inertia subgroup and `A` is the discrete algebraic-closure
  units. That application is not part of this statement.
