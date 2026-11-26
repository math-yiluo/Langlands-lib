# Quasi-étale base change from local domain–étale factorizations

This module proves two unconditional results and one conditional reduction,
in the namespace `Langlands.Analytic.SaturatedAtlasPresentation`, for a
complete ultrametric normed field `K : Type u` and the localized category
`LocalizedCategory.{u, v, v} (K := K)`.

- Étale arrows are stable under base change along every pullback square
  (`localizedEtaleBaseChange`).
- A quasi-étale arrow with a Hausdorff source stays quasi-étale after base
  change (`quasiEtale_of_isPullback_of_t2Space`).
- `QuasiEtaleBaseChangeStatement K` follows from
  `QuasiEtaleLocalDomainFactorizationsStatement K`
  (`quasiEtaleBaseChange_of_localDomainFactorizations`).

The last result is conditional. Its hypothesis is a Library proposition that
this module does not prove. This module does not prove
`QuasiEtaleBaseChangeStatement` unconditionally. For a Hausdorff source of
the quasi-étale leg, base change is proved outright, by the second result.

## Declarations

### `localizedEtaleBaseChange : LocalizedEtaleBaseChangeStatement.{u, v} K`

`LocalizedEtaleBaseChangeStatement K` (module `QuasiEtalePullbackLocality`) is
the Mathlib class `MorphismProperty.IsStableUnderBaseChange` for `etale` on
`LocalizedCategory.{u, v, v} (K := K)`. Its field `of_isPullback` takes a
square `sq : IsPullback f' g' g f` with `g : Y ⟶ S` étale and asks that
`g' : Y' ⟶ X` is étale.

Proof. The published theorem `localizedEtalePullbackBaseChange` (module
`LocalizedEtalePullbackProof`), applied to the étale arrow `g` and to `f`,
gives some square `IsPullback p q g f` whose second projection `q` is étale.
The Library lemma `etale_snd_of_isPullback` (module
`EtaleBaseChangeReduction`) compares two pullback squares of the same cospan.
It carries `etale q` to `etale g'` through the canonical isomorphism of the
two corners.

### `quasiEtale_of_isPullback_of_hasLocalDomainEtaleFactorizations`

Hypotheses: a square `sq : IsPullback f' g' g f` with `f : X ⟶ S`,
`g : Y ⟶ S`, `f' : Y' ⟶ Y`, `g' : Y' ⟶ X`, and
`HasLocalDomainEtaleFactorizations g`. Conclusion: `quasiEtale g'`.

Proof. Install `localizedEtaleBaseChange` as the instance
`etale.IsStableUnderBaseChange`. Under that instance the Library theorem
`HasLocalDomainEtaleFactorizations.of_isPullback` (module
`QuasiEtalePullbackLocality`) transports the factorizations of `g` to `g'`
along `sq`. It uses the inverse-image domains under `f'`. Then
`HasLocalDomainEtaleFactorizations.quasiEtale` (module
`QuasiEtaleDomainLocality`) turns them into `quasiEtale g'`.

### `quasiEtale_of_isPullback_of_t2Space`

Hypotheses: a square `sq : IsPullback f' g' g f` as above,
`[T2Space (localizedSpaceFunctor.obj Y)]`, and `quasiEtale g`. Conclusion:
`quasiEtale g'`.

Proof. The Library theorem `hasLocalDomainEtaleFactorizations_of_quasiEtale`
(module `QuasiEtaleDomainLocality`) gives
`HasLocalDomainEtaleFactorizations g` for the Hausdorff source `Y`. Apply the
previous theorem.

The Hausdorff hypothesis is on the source `Y` of the quasi-étale leg only.
Nothing is assumed about `X`, `S` or `Y'`.

This theorem is the content of `QuasiEtaleHausdorffBaseChangeStatement`
(module `QuasiEtaleHausdorffStabilityStatement`), the base change clause of
Berkovich 1994, Lemma 3.1(i), for a Hausdorff source. The module
`QuasiEtaleHausdorffBaseChangeProof` proves that statement from it
(`quasiEtaleHausdorffBaseChange`).

### `quasiEtaleBaseChange_of_localDomainFactorizations`

Hypothesis: `h : QuasiEtaleLocalDomainFactorizationsStatement.{u, v} K`, the
proposition that every quasi-étale arrow of the localized category, with any
source, has local domain–étale factorizations through every point (module
`QuasiEtaleLocalDomainFactorizationsStatement`). Conclusion:
`QuasiEtaleBaseChangeStatement.{u, v} K`.

Proof. For a square `sq : IsPullback f' g' g f` with `quasiEtale g`, the
hypothesis gives `HasLocalDomainEtaleFactorizations g`, and
`quasiEtale_of_isPullback_of_hasLocalDomainEtaleFactorizations` gives
`quasiEtale g'`. The result covers every pullback square. No Hausdorff,
compactness, smallness or chosen-limit hypothesis is placed on any object.

It is declared with `def` under `set_option linter.defProp false`, although
its type is a proposition, so that it can be recorded as a supporting
definition artifact. The Library's `etaleBaseChange_of_descent` is declared
the same way.

## Universes

`u` is the universe of the field, and `v` is the universe of spaces and atlas
indices. These match `QuasiEtaleBaseChangeStatement.{u, v}`,
`LocalizedEtaleBaseChangeStatement.{u, v}` and
`LocalizedEtalePullbackStatement.{u, v}`.

## Provenance

Internal. These are reductions within the Library's vocabulary and transcribe
no external statement. The target `QuasiEtaleBaseChangeStatement` is the base
change clause of Berkovich, *Vanishing cycles for formal schemes* (1994),
Lemma 3.1(i), printed p.544. Berkovich derives Lemma 3.1 from the properties
of étale morphisms and from Berkovich 1993, Theorem 3.4.1. This module uses
étale base change in the same way. In place of Theorem 3.4.1 it needs the
pointed form of the quasi-étale condition, which is the hypothesis
`QuasiEtaleLocalDomainFactorizationsStatement`. That module's Markdown
explains why the Library's nonpointed definition requires it for a
non-Hausdorff source. It also records a proof of the general case in the
literature: Ducros, *Families of Berkovich spaces*, Lemma 5.4.11, which
rests on Ducros's Theorem 5.4.6 (whose proof uses the analytic Zariski Main
Theorem) and on Berkovich 1993, Theorem 3.4.1. That page also explains what
a direct gluing of étale envelopes would require beyond Theorem 3.4.1.
