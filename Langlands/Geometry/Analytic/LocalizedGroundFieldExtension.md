# Ground field extension of localized analytic spaces

`localizedFunctor K L` extends a saturated analytic atlas and its morphisms
from a complete ultrametric normed field \(K\) to a complete ultrametric
normed \(K\)-algebra field \(L\). The construction includes trivial
valuations and arbitrary extension degree. The original chart index
universe and the two field universes may differ.

On an original saturated presentation this is `saturatedLocalizedFunctor`.
It extends each affinoid algebra and bounded pullback, glues the extended
charts, saturates the resulting atlas, and sends it to the localized
category. Saturation preserves full quasi-isomorphisms, and
`groundFieldExtensionQuasiIso` proves that extension of the compatible
strong map also preserves them. The strict localization factorization
therefore determines `localizedFunctor` and its value on each original
strong map.

`localizedProjection` is the natural continuous map from the underlying
scalar-extended space to the original underlying space. A universe lift at
each end puts the spaces in the same category of topological spaces.
`localizedProjection_app` identifies each component with the glued
projection given by restriction of the chart seminorms. The strong-map
naturality of this projection extends to all localized morphisms by the
localization property for natural transformations.

The construction supplies analytic scalar extension and projection for
the comparison in Conrad–Temkin, *Non-archimedean analytification of
algebraic spaces*, Theorem 2.3.5 (p. 13), source
`conrad-temkin-2009-nonarchimedean-analytification`, SHA-256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`.
Conrad uses the comparison in the proof of Proposition 5.11(3) on p. 19 of
*Weil and Grothendieck approaches to adelic points*, source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
