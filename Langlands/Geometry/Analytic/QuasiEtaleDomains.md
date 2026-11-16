# Quasi-étale inclusions of analytic domains

This internal development proves that the canonical inclusion of every actual
analytic domain is quasi-étale. It works over a complete ultrametric normed
field, with the analytic domains and localized category already defined in
`AnalyticDomainSpaces` and `InvariantAnalyticDomains`. The restriction and
nested-chart helpers allow distinct space and atlas universes `v` and `w`;
the quasi-étale results use the equal-universe category required by
`QuasiEtaleSite`.

`domainRestrictIso` restricts an isomorphism of localized analytic spaces to
domains carried into one another by the isomorphism and its inverse. The
restriction triangles and monicity of the actual inclusions prove the inverse
laws. Its forward inclusion triangle is recorded by
`domainRestrictIso_hom_inclusion`. The required image conditions are explicit
inputs; this construction asserts no general preservation of analytic domains
under arbitrary maps.

`isAffinoidDomainEmbedding_domainInclusion_comp` identifies an original chart of
a domain with the same original chart of the ambient presentation. The
published nested-domain isomorphism supplies the comparison of the actual
objects and complete arrows; equality of the ambient subsets identifies the
result with the ambient chart-domain inclusion. The auxiliary
`eqToIso_hom_domainInclusion` records compatibility of the canonical inclusion
with transport along equality of domains.

`isAffinoidDomainEmbedding_saturationChart_domainInclusion` handles a chart of
the constructed saturation of the domain presentation. Because the domain
atlas contains all local full domains, that chart has the same range as an
original chart of the domain. Restricting the actual saturation isomorphism
to these two domains gives an isomorphism compatible with their inclusions.
The preceding nested-chart result then identifies the composite with an
affinoid domain embedding into the ambient localized space. The proof uses
the published quotient-domain factorization and comparison functor; equality
of underlying point maps alone is not used to establish equality of arrows.

For `quasiEtale_localizedDomainInclusion`, let `N = S.domain D`. The explicit
strong representative between constructed saturations is

```text
N.saturationIso.hom ≫ S.domainInclusion D ≫ S.saturationIso.inv.
```

At every source point, the source chart net supplies the finite chart
neighborhood required by `IsQuasiEtaleAt`. For each chart take the intervening
space to be the localization of `S`, and take its étale arrow to be the image
of `S.saturationIso.inv`, which is an isomorphism. The preceding theorem gives
the affinoid domain embedding into this space. Functoriality proves the
required triangle. Finally, the localized saturation isomorphisms identify
the representative with the canonical domain inclusion in the arrow category.
`quasiEtale_domainι` restates this result for a domain of any localized object.

The provenance is internal: the proof combines the published domain
factorization, monicity, restriction and nested-domain isomorphisms with
`HasAllLocalDomains.exists_chart`, the source chart net, the actual saturation
isomorphism and `etale_of_isIso`. It assumes no unproved Library proposition.
It requires no compactness or group action. General quasi-étale composition
and base-change stability, categorical pullbacks, finite Čech presentations
and the compact equivariant cohomology comparison remain separate obligations.
