# Proof: quasi-étale base change for Hausdorff sources

The module proves
`Langlands.Analytic.SaturatedAtlasPresentation.quasiEtaleHausdorffBaseChange`,
whose type is `QuasiEtaleHausdorffBaseChangeStatement.{u, v} K` (module
`QuasiEtaleHausdorffStabilityStatement`) for every complete ultrametric
normed field `K : Type u`.

## Proof

Take a pullback square `IsPullback f' g' g f` of the localized category, with
`g : Y ⟶ S` quasi-étale and the underlying space of `Y` Hausdorff. The
Hausdorff hypothesis is made available as an instance, and the Library
theorem `quasiEtale_of_isPullback_of_t2Space` (module
`QuasiEtaleBaseChangeReduction`) gives that `g'` is quasi-étale.

That theorem works as follows. For a Hausdorff source,
`hasLocalDomainEtaleFactorizations_of_quasiEtale` (module
`QuasiEtaleDomainLocality`) gives at each point finitely many analytic
domains through the point whose union is a neighbourhood, each with a
factorization of the restricted arrow as an analytic-domain embedding
followed by an étale arrow. `HasLocalDomainEtaleFactorizations.of_isPullback`
(module `QuasiEtalePullbackLocality`) pulls these back along the square,
using étale base change along every pullback square
(`localizedEtaleBaseChange`, from `localizedEtalePullbackBaseChange`), and
`HasLocalDomainEtaleFactorizations.quasiEtale` turns the result into the
quasi-étale predicate for `g'`.

## Scope

Only the source `Y` of `g` is assumed Hausdorff; nothing is assumed of `X`,
`S` or `Y'`. The proof uses no unproved proposition of the Library.
