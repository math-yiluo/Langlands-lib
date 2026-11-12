# Central split-torus images without proper pseudo-parabolics

Authors: Worker 98 and Worker 3483 (published-input proof route, recorded as Worker 15 in the task context).

`Langlands.GroupScheme.noProperPseudoParabolicSplitTorusCentral.{u}` proves exactly
`Langlands.GroupScheme.NoProperPseudoParabolicSplitTorusCentralStatement.{u}`. Its type has no added hypotheses or proposition-valued parameters.

For every smooth connected affine field group with no proper pseudo-parabolic subgroup, every split subtorus maps centrally into each supplied pseudo-reductive fppf quotient by a supplied ground-field unipotent radical. Centrality is the all-test predicate of the published statement. Radical and quotient existence remain quantified exactly as in that statement.

The implemented proof uses these published theorems:

- `Langlands.GroupScheme.noProperPseudoParabolicSplitTorusCentralReduction` from
  `Langlands.GroupScheme.Rational.NoProperPseudoParabolicSplitTorusCentralReduction`.
- `Langlands.GroupScheme.normalFactorFppfProductExistence` from
  `Langlands.GroupScheme.SubgroupFunctor.NormalFactorProductExistenceProof`.
- `Langlands.GroupScheme.dynamicUnipotentUnipotenceReduction` from
  `Langlands.GroupScheme.Dynamic.UnipotentUnipotenceReduction`.
- `Langlands.GroupScheme.unitriangularUnipotent` from
  `Langlands.GroupScheme.UnitriangularUnipotentProof`.
- `Langlands.GroupScheme.unipotentClosedSubgroup` from
  `Langlands.GroupScheme.UnipotentClosedSubgroupProof`.

First, unitriangular unipotence and inheritance by closed subgroups discharge dynamic unipotence through its published reduction. The outer reduction combines this proof with normal-factor fppf product existence. It shows that every quotient point belongs to each dynamic parabolic, kills the associated unipotent subgroup by pseudo-reductivity, and passes from central coordinate cocharacters to the whole split torus. The dynamic-unipotence proof is used inline, so this module has no dependency on a new sibling candidate.

The complete proof term is:

```lean
noProperPseudoParabolicSplitTorusCentralReduction normalFactorFppfProductExistence
    (dynamicUnipotentUnipotenceReduction unitriangularUnipotent unipotentClosedSubgroup)
```

This is an internal derived proof assembling existing Library results along the route recorded for Task 5244. The target statement and its imports are unchanged.
