# Conditional existence of analytifications of separated algebraic spaces

This module is a conditional assembly with derived provenance. It derives the published
`SpaceAnalytificationExistenceStatement` from explicit hypotheses, following the route of
Conrad–Temkin (2009), §4.2–4.3. **The target statement is not proved**: the seven inputs of
`SpaceAnalytificationExistenceReductionStatement` are still hypotheses, and none of them is
proved in the Library.

## Declarations

- `isAnalytification_pointFamily`: the glued point family `pointFamily H hX E` of a
  `QuotientData` is an analytification (`IsAnalytification`). Its four fields come from
  `SpaceAnalytificationExistenceConstruction` (naturality, étale maps, joint surjectivity) and
  `SpaceAnalytificationExistencePullback` (fibre squares go to pullbacks).
- `exists_isAnalytification`: an analytification exists given `AnalyticInputs K`, a separated
  `X` and a `QuotientData D` for some `ChartData X`.
- `spaceAnalytificationExistenceStatement_of_inputs` takes two hypotheses:
  - `hQuot`: every `ChartData` of a separated algebraic space over every field has a
    `QuotientData`;
  - `hInputs`: `AnalyticInputs K` holds for every complete, ultrametric, nontrivially
    normed `K`.

  From these it proves `SpaceAnalytificationExistenceStatement.{u}`. The chart family is
  constructed unconditionally by `nonempty_chartData`.
- `SpaceAnalytificationExistenceReductionStatement` (the entry declaration) is a
  proposition. It says that seven inputs, taken in the order below, imply
  `SpaceAnalytificationExistenceStatement.{u}`. Two inputs are already Library statements:
  - input 4: `AffineAnalytificationFibreProductStatement.{u,u,u,u}`. Together with the
    published theorem `affineAnalytificationLocalizedFunctoriality`, it supplies the
    `affPullback` field of `AnalyticInputs` through `isPullback_localizedHom_of_isPullback_ty`.
  - input 6: `LocalizedEtalePullbackStatement.{u,u} K` for every `K`.

  The other five inputs are not yet in the Library, so they are written out in full. Each
  one is literally the body of the named proposal at the stated universes, so the proposal
  can be supplied directly once it is published.
  - input 1: the proposed `SpaceAnalytificationChartQuotientStatement`. Every family of
    étale affine test points `xᵢ : Spec Aᵢ → X` of a separated `X` has a quotient. That is,
    there are an analytic space `Y` and étale maps `πᵢ : Spec(Aᵢ)ᵃⁿ → Y`, jointly surjective
    on points, which carry every presheaf fibre square `Spec B = Spec Aᵢ ×_X Spec Aⱼ` to a
    pullback square. This is the chart form of Conrad–Temkin, Theorem 4.2.2.
  - input 2: Worker 790's proposed `EtaleHomSheafStatement.{u,u}`. Morphisms to an analytic
    space `T` form a sheaf on the small étale site of every analytic space. This is
    representable étale descent (Berkovich 1993, §4.1; Conrad–Temkin 2009, Theorem 4.1.2
    and the discussion around it).
  - input 3: Worker 550's proposed `LocalizedEtaleSourceDescentStatement.{u,u,u}`.
    Étaleness descends through a jointly surjective family of étale maps to the source.
  - input 5: the proposed `AffineAnalytificationLocalizedEtaleStatement.{u,u,u}`. The
    analytification of an étale map of finitely presented `K`-algebras is étale (Berkovich
    1990, Proposition 3.4.6(3)).
  - input 7: the proposed `AffineAnalytificationJointSurjectivityStatement.{u,u,u}`. If a
    family of algebra maps is jointly surjective on prime spectra, its analytified family
    is jointly surjective on underlying points. This follows from Berkovich (1990),
    Proposition 3.4.6(7) and the fibre isomorphism (*) in its proof.
- `spaceAnalytificationExistenceReduction` proves
  `SpaceAnalytificationExistenceReductionStatement.{u}`. Input 1 gives `hQuot` of
  `spaceAnalytificationExistenceStatement_of_inputs`, by reading the quotient of the chart
  family of a `ChartData` as a `QuotientData`. The remaining inputs fill the fields of
  `AnalyticInputs K`. Two fields need no hypothesis because published theorems supply them:
  - `comp` and `id` come from `affineAnalytificationLocalizedFunctoriality`, which proves
    `AffineAnalytificationLocalizedFunctorialityStatement`;
  - `points` (compatible pairs of underlying points lift to the apex of a pullback square
    with an étale leg) comes from `exists_point_of_isPullback` in `LocalizedPullbackPoints`,
    which needs no étale premise.

## Scope

All objects live in the Library's localized category `LocalizedCategory.{u,u,u}` over a field
`K : Type u`. The chart family, the affine models of fibre squares and the presheaf-model form
of affine fibre products are proved without analytic hypotheses beyond input 4 and the
published localized functoriality; see
`SpaceAnalytificationExistenceCharts`, `SpaceAnalytificationExistenceAffineModels` and
`SpaceAnalytificationExistenceAffinePullbacks`.
