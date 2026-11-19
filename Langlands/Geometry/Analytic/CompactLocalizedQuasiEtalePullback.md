# Compactness of localized pullbacks along quasi-étale morphisms

Let `f : A ⟶ X` be quasi-étale and let `g : B ⟶ X` be any morphism in
`LocalizedCategory.{u,v,v}`. If `A` and `B` are compact Hausdorff and `X` is
Hausdorff, the source of any full analytic pullback of `f` and `g` is compact
Hausdorff. `compactLocalizedQuasiEtalePullback` packages this property with the
cone and limit already chosen by `localizedQuasiEtalePullback`.

The proof first expresses `f` by the strong quasi-étale representative in its
definition. A right fraction for `g` gives a strong map to the same
representative base. The localized isomorphisms transport the supplied
pullback square and the topological hypotheses to this cospan.

Recognition gives a second diagram of strong maps whose glued product is
small by `small_recognition_fibreProductSpace_of_domainEtaleCharts`. Its small
saturated presentation is compact Hausdorff by
`isCompactSpace_localization_smallFibreProduct`. The uniqueness isomorphism
between the two limiting cones transfers that property to the supplied point.

This is an internal consequence of the Library's localized pullback
construction and compactness theorem for the glued product.
