# Geometric solvable radicals of reductive groups from central tori

Author: Worker 1378.

This module reduces the published target
`ReductiveGeometricSolvableRadicalExistsStatement.{u}` (module
`Rational.ReductiveGeometricSolvableRadicalExistsStatement`) to three
published structure statements, and proves the reduction. It proves none of
the three statements, so it does not discharge the target.

## The reduction statement

`ReductiveGeometricSolvableRadicalFromStructureStatement.{u}` is the
Prop-valued implication

```
SolvableRadicalExistenceStatement.{u} →
  AlgClosedReductiveNormalSolvableTorusStatement.{u} →
    ReductiveLargestCentralSubtorusBaseChangeStatement.{u} →
      ReductiveGeometricSolvableRadicalExistsStatement.{u}
```

All four propositions are published and used unchanged:

- `SolvableRadicalExistenceStatement` (module
  `Rational.SolvableRadicalExistenceStatement`): every smooth affine connected
  group scheme over a field has a solvable radical `IsSolvableRadical r` over
  that field;
- `AlgClosedReductiveNormalSolvableTorusStatement` (module
  `Rational.AlgClosedNormalSolvableTorusStatement`): over an algebraically
  closed field, a smooth connected solvable closed subgroup with normal range
  in a pseudo-reductive group is a torus and is central;
- `ReductiveLargestCentralSubtorusBaseChangeStatement` (module
  `Rational.LargestCentralSubtorusBaseChangeStatement`): a largest central
  subtorus of a connected reductive group stays a largest central subtorus
  after every field extension;
- the conclusion is the target: every connected reductive group `G` over a
  field `k` has some `r : R → G` with `IsGeometricSolvableRadical r`, so `r`
  is the solvable radical over `k`, and its base change to the algebraic
  closure `k̄` is the solvable radical of `G_{k̄}`.

All four statements share the universe parameter. Fields and groups are
arbitrary, and the reduction adds no perfectness, splitness or
characteristic restriction.

## The proof

`reductiveGeometricSolvableRadicalExists_of_structure` proves the
implication. Let `G` be connected reductive over `k`, and write `b` for the
base change along `Spec k̄ → Spec k`.

1. `G` is smooth, affine and connected. The first hypothesis then gives
   `r : R → G` with `IsSolvableRadical r`.
2. `isGeometricSolvableRadical_of_structural` shows that `r` is a geometric
   solvable radical:
   - `G_{k̄}` is pseudo-reductive. Smoothness and affineness are stable
     under base change. Connectedness is
     `connectedSpace_baseChange_of_smooth_affine`. Triviality of the
     unipotent radical is the geometric half of `IsConnectedReductive`.
   - The base change `r_{k̄}` is a closed subgroup (`IsClosedSubgroup.baseChange`).
     `R_{k̄}` is smooth, and it is connected by the same connectedness
     lemma. It is solvable, by three lemmas in the `RelativeRoot` namespace
     of `Rational.SolvableSchemeComparison`:
     `isSolvableScheme_iff_isSolvableGroupScheme` turns geometric-point
     solvability into scheme solvability, `IsSolvableScheme.baseChange`
     moves that to `k̄`, and `IsSolvableScheme.isSolvableGroupScheme` turns
     it back. The range of
     `r_{k̄}` is normal by `range_baseChangeHom` and
     `SubgroupFunctor.IsNormal.baseChange`.
   - The second hypothesis, applied to `r_{k̄}` in `G_{k̄}`, shows that
     `R_{k̄}` is a torus and `r_{k̄}` is central. Then `IsTorus.of_baseChange`
     makes `R` a torus, and `IsCentral.of_baseChange` (fpqc reflection along
     `k → k̄`) makes `r` central.
   - So `r`, with `R` viewed as a commutative group scheme through
     `IsTorus.isCommMonObj`, is a largest central subtorus of `G` over `k`.
     Greatestness comes from `range_le_of_isSolvableRadical`. A central
     closed subtorus `a` is a competitor for `IsSolvableRadical.greatest`:
     it is smooth and connected because it is a torus
     (`IsTorus.smooth`, `IsTorus.connectedSpace`), solvable because it is
     commutative (the existing
     `Langlands.GroupScheme.isSolvableGroupScheme_of_isCommMonObj` in
     `Torus.Geometry`), and its range is
     normal because it is central (`IsCentral.range_isNormal`).
   - The third hypothesis, applied with `K = k̄`, makes `r_{k̄}` a largest
     central subtorus of `G_{k̄}`.
   - For greatestness over `k̄`, let `n : N → G_{k̄}` be a smooth connected
     solvable closed subgroup with normal range. The second hypothesis
     makes `N` a torus and `n` central. The largest-central-subtorus
     property of `r_{k̄}` then gives range containment on every test scheme.

   Together with the ground-field property from step 1, these give every
   field of `IsGeometricSolvableRadical r`.

## Provenance

This is a derived internal reduction. Its route follows the proof of Milne,
*Algebraic groups* (2017), Corollary 17.62(b),(c), printed pp.372-373. There
the radical of a reductive group is identified with the largest central
subtorus, and its formation commutes with field extension. The source content
of the three hypotheses is documented in their own statement Markdown. This
module adds no new citation and no new external structural assertion. The
hypotheses are explicit premises of the implication and are not proved here.
