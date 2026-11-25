# A geometric comparison for supplied reductive integral models: proof

Lean module: `Langlands.GroupScheme.IntegralModel.BuildingComparisonProof`,
namespace `Langlands.GroupScheme.IntegralModel`.

## Statement

```
theorem Langlands.GroupScheme.IntegralModel.buildingComparison :
    BuildingComparisonStatement.{u}
```

The type is exactly the published proposition
`Langlands.GroupScheme.IntegralModel.BuildingComparisonStatement.{u}` of the
module `Langlands.GroupScheme.IntegralModel.BuildingComparison`, at an
arbitrary universe `u`, with no further hypothesis. Unfolded, it reads:

```
∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
  (M : IntegralModel ↥𝒪[F] F G),
  IsConnectedReductive
    ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group) →
  letI : IsAffineHom G.X.hom := hG.isAffineHom
  Nonempty (BuildingComparison M)
```

In words: for every connected reductive group `G` over a nonarchimedean local
field `F` and every integral model `M` of `G` over `𝒪[F]` whose special fibre
is connected reductive, there is a `BuildingComparison M`: valuation building
data of `G` whose reduced building carries a complete metric, nonpositively
curved in the KP midpoint sense, on which `G(F)` acts by isometries with
continuous orbit maps, together with a special vertex `x` such that the image
of the integral points of `M` is the compact stabilizer of `x` (the common
norm-one kernel of the rational characters intersected with the fixer of `x`)
and `x` is the only point that image fixes.

## Proof

The Lean proof is the single application

```
buildingComparisonStatement_of_unramified
  Langlands.Geometry.Building.rootValuationBuildingConstruction unramifiedSpecialStabilizer
  (Langlands.Geometry.Building.unramifiedBuildingDescentStatement_of_apartmentDescent
    Langlands.Geometry.Building.unramifiedApartmentDescent)
```

of `buildingComparisonStatement_of_unramified` (module
`GroupScheme.IntegralModel.BuildingComparisonUnramifiedReduction`), which
derives the statement from three hypotheses. Each is discharged by theorems
proved in the Library without hypotheses:

1. `Langlands.Geometry.Building.rootValuationBuildingConstruction` (module
   `Geometry.Building.RootValuationBuildingConstructionProof`): the
   root-valuation building with the five axiom families of the metric
   construction.
2. `unramifiedSpecialStabilizer` (module
   `GroupScheme.IntegralModel.UnramifiedSpecialStabilizerProof`): over the
   maximal unramified extension, the image of the integral points is the
   norm-one stabilizer of a special point, which is the only point it fixes.
3. `UnramifiedBuildingDescentStatement.{u}`, given by
   `Langlands.Geometry.Building.unramifiedBuildingDescentStatement_of_apartmentDescent`
   (module `Geometry.Building.UnramifiedApartmentDescentStatement`) applied to
   `Langlands.Geometry.Building.unramifiedApartmentDescent` (module
   `Geometry.Building.UnramifiedApartmentDescentProof`): the building embeds
   equivariantly onto the Galois-fixed points of the building over the maximal
   unramified extension, reflecting special points.

Inside the reduction, the second and third statements give the special
stabilizer statement over `F`, and with the building construction and its
metric the comparison datum is assembled; the details are on the page of
`GroupScheme.IntegralModel.BuildingComparisonUnramifiedReduction`. The
statement is not modified and no hypothesis is added.

## Declarations

- `Langlands.GroupScheme.IntegralModel.buildingComparison :
  BuildingComparisonStatement.{u}`.

## Literature

The statement's page records an internal provenance and cites no source. The
route of the reduction is that of F. Bruhat and J. Tits, *Groupes réductifs
sur un corps local, II. Schémas en groupes. Existence d'une donnée radicielle
valuée*, Publ. Math. IHÉS 60 (1984), §5.1, Proposition 5.1.40, printed p. 161:
it characterizes the smooth models with reductive closed fibre by a special
point `x` whose group scheme is isomorphic to the model; the proof deduces it
from 4.6.31, uses that `x` is the only fixed point of the model's integral
points (4.6.29), and descends `x` by Galois invariance.
