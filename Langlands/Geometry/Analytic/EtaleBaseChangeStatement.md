# Statement: étale morphisms are stable under base change

Author: Worker 21.

This module states, without proof, that the base change of an étale morphism
along any morphism is étale, for the fibre products of `AnalyticFibreProduct`.

## The statement

`EtaleBaseChangeStatement : Prop` (namespace
`Langlands.Analytic.SaturatedAtlasPresentation`). Let `K` be a complete,
ultrametric normed field in universe `u`. Let `X`, `Y`, `S` be saturated
presentations in `SaturatedAtlasPresentation.{u, u, u} K` whose spaces are
Hausdorff, and let `f : X ⟶ S` and `g : Y ⟶ S` be strong maps. If the image of
`f` in the localized category is étale (the published predicate `etale` of
`EtaleSite`), then so is the image of the second projection
`fibreProductSnd f g : X ×_S Y → Y`.

`etale` holds for a morphism of the localized category when it is isomorphic,
as an arrow, to the image of a strong map between saturations whose pieces are
quasi-finite, flat and unramified (`StrongHom.IsEtaleAllPieces`, Berkovich 1993
Definition 3.3.4).

## Original source

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`,
Corollary 3.3.8, printed p.63 / PDF p.60: "Unramified (resp. étale) morphisms
are preserved under compositions, under any base change functor, and under any
ground field extension functor."

The statement transcribes the base-change part for the Library's fibre
products. Derived choices: the hypotheses (strong maps of saturated
presentations with Hausdorff spaces, equal universes) are those of
`AnalyticFibreProduct`. Base change along a general morphism of the localized
category reduces to this case once fibre products are known to be pullbacks
(`FibreProductPullbackStatement`), because every morphism there is a fraction
of strong maps.

## Scope

This is a `lean.statement`: nothing is proved here. It is needed for the
pullback of étale sites along morphisms (Berkovich 1996, §1.2) and for étale
neighbourhoods of geometric points.
