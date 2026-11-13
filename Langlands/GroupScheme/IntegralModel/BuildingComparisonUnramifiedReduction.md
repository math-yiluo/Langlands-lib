# The building comparison from its maximal unramified form and descent

This module states the reduction proposition
`Langlands.GroupScheme.IntegralModel.BuildingComparisonUnramifiedReductionStatement`
and proves it (`buildingComparisonUnramifiedReduction`). It also proves the
intermediate implication `specialStabilizerStatement_of_unramified`. It proves
none of the inputs, so it does not prove
`Langlands.GroupScheme.IntegralModel.BuildingComparisonStatement`.

## The statement

`BuildingComparisonUnramifiedReductionStatement.{u}` is the implication

```
RootValuationBuildingConstructionStatement.{u} →
  UnramifiedSpecialStabilizerStatement.{u} →
    UnramifiedBuildingDescentStatement.{u} →
      BuildingComparisonStatement.{u}
```

between four published propositions, at the same universe `u`:

* `Langlands.Geometry.Building.RootValuationBuildingConstructionStatement`:
  every connected reductive `G` over a nonarchimedean local field has a
  `ParahoricBuildingData G` with a polysimplicial realization, an apartment
  splitting and the seven axiom predicates;
* `Langlands.GroupScheme.IntegralModel.UnramifiedSpecialStabilizerStatement`:
  for a supplied model `M` with connected reductive special fibre, and every
  building datum `C` over the maximal unramified extension
  `K = inertiaFixedField F`, the image of the integral points of the base change
  `M.baseChangeUnramified` is the norm-one stabilizer `C.oneStabilizer x` of a
  special point `x`, and `x` is the only point that image fixes;
* `Langlands.Geometry.Building.UnramifiedBuildingDescentStatement`: every
  `B : ValuationBuildingData G` embeds injectively and equivariantly, by some
  `e`, into the quotient of a building datum `C` over `K` carrying a semilinear
  Galois action `D`; every Galois-fixed point upstairs lies in the image of `e`;
  and `z` is special whenever `e z` is;
* `Langlands.GroupScheme.IntegralModel.BuildingComparisonStatement`: the exact
  target of this task.

The statement adds no hypothesis to any of the four propositions. Its
provenance is internal: it records how the Library's published statements
compose, and asserts nothing beyond them. The mathematical route it formalizes
is that of Bruhat–Tits II (1984), Proposition 5.1.40 (printed p. 161 /
PDF p. 158), which proves the comparison over the strict Henselization through
4.6.31 and 4.6.28–4.6.29 and then descends; the two unramified inputs are the
Library's statements of those two steps.

## The proofs

`specialStabilizerStatement_of_unramified` proves the published
`SpecialStabilizerStatement.{u}` from `UnramifiedSpecialStabilizerStatement.{u}`
and `UnramifiedBuildingDescentStatement.{u}`. Given `F`, `G`, `hG`, `M`, the
special-fibre hypothesis, `P : ParahoricBuildingData G` and its seven
predicates (which this step does not use):

1. Descent applied to `P.toValuationBuildingData` gives `C`, `D`, the
   injective equivariant embedding `e`, the fixed-point property `hfix` and
   special-point descent `hspec`.
2. The unramified identity applied to `M` and this `C` gives a special point
   `x` with `M.baseChangeUnramified.integralPoints = C.oneStabilizer x` and the
   uniqueness property `hunique`.
3. Every element of the upstairs image fixes `x`, by that equality and
   `IntegerValuationBuildingData.mem_oneStabilizer`.
4. The published
   `IntegralModel.unramifiedIntegralImage_semilinearAction_eq_of_unique_fixed`
   turns this and `hunique` into `D.action σ x = x` for every
   `σ : K ≃ₐ[F] K`. So `hfix` gives `z` with `e z = x`.
5. `hspec` makes `z` special for `P`. The published
   `IntegralModel.integralPoints_eq_compactStabilizer_of_unramified` turns
   `M.baseChangeUnramified.integralPoints = C.oneStabilizer (e z)`, injectivity
   and equivariance of `e` into `M.integralPoints = P.compactStabilizer z`.

That lemma states equivariance with `UnramifiedClosure F`, a reducible
abbreviation of `inertiaFixedField F`. The proof first restates the descent
equivariance in that form (`he'`), because unifying the two forms inside the
application is slow. For the same reason the theorem raises `maxHeartbeats`
to 800000.

`buildingComparisonStatement_of_unramified` feeds this into the published
`buildingComparisonStatement_of_specialStabilizer`, together with
`RootValuationBuildingConstructionStatement.{u}`.
`buildingComparisonUnramifiedReduction` is this theorem in the form of the
reduction statement.

## Scope

None of `RootValuationBuildingConstructionStatement`,
`UnramifiedSpecialStabilizerStatement` and
`UnramifiedBuildingDescentStatement` is proved here, so this module proves
neither `SpecialStabilizerStatement` nor `BuildingComparisonStatement`. Once
the three inputs are proved, the target is the term
`buildingComparisonStatement_of_unramified hcon hstab hdesc`.
