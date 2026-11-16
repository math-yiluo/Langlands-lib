# Finite wide pullbacks of actual quasi-étale domain charts

Work over a complete ultrametric normed field, with equal space and chart
universes. Let `C` be a `FiniteCompactDomainChartCover U` in the actual
quasi-étale site over `X`. For a finite index type `J`, a tuple
`a : J → C.Index` and a chosen member `j₀ : J`, `wideDomain a j₀` is the
anchored intersection of the domains selected by the tuple. Repeated chart
indices are allowed. The anchor provides the retained domain-étale
factorization from the earlier intersection construction. Membership is
equivalent to membership in every selected domain.

`wideObj` is the resulting actual quasi-étale site object.
`wideBase` maps it to `U`. Each `wideProjection` is the actual domain-order
map followed by the inverse of the selected source's stored domain
isomorphism. The projection followed by its cover arrow equals the base
arrow as an equality of complete site morphisms. These maps define
`wideCone`, a wide pullback cone over the tuple of cover arrows.

`wideIsLimit` proves its universal property against every quasi-étale site
object. A cone's common ambient arrow takes values in each selected domain,
by the cone equations and the full domain-isomorphism triangles. The
actual analytic-domain factorization API constructs `wideLift` through the
intersection. Monicity of the ambient inclusion proves the base equation
and uniqueness. Each cover arrow is monic because it is a domain
inclusion composed with an isomorphism, so the base equation implies all
projection equations. No compactness assumption is imposed on the test
object.

If the ambient underlying space of `U` is Hausdorff, the representing
object is compact Hausdorff by the previously proved anchored finite
intersection theorem. Thus nonempty finite tuples of these domain-chart
arrows have compact actual wide pullbacks under that hypothesis.

This is internal geometric infrastructure derived from the existing
domain-chart and intersection APIs and the ordinary categorical wide
pullback definition. It handles domain-chart arrows. It does not establish
pullbacks for arbitrary quasi-étale arrows, continuity of a restricted
Berkovich group action, compatible lifted Čech presentations, or the
global cohomological comparison theorem.
