# Localized analytic maps glued on domains

`LocalizedDomainMatchingFamily` is a family of maps in the existing localized
analytic category from original-chart domains of a saturated atlas to a
second saturated atlas. Its overlap equation is equality of analytic
morphisms after restriction to the actual intersection of the two domains.
`localizedDomainMap` uses the existing inclusion of nested domains in the
explicit source quotient. Composing with either inclusion into the ambient
space gives the inclusion of the smaller domain.

For a quasinet cover, `LocalizedDomainMatchingFamily.glue` takes these maps
to the explicit source quotient via the fully faithful comparison functor.
It uses `QuotientDomainMatchingFamily.glue` there and maps the result back.
`glue_restrict` recovers the input morphisms. The companion
`localizedHom_ext_of_domainCover` transfers uniqueness the same way.
Field, space, chart and cover universes are independent. The field is
complete and ultrametric with a norm.

This is an internal transport of the Library's `QuotientDomainGluing` and
`SaturatedSourceDomainSeparation`, using `SourceCategory.comparisonFunctor`
and the domain inclusion comparison in `InvariantAnalyticDomains`. Thus
all morphism equalities retain the bounded algebra pullbacks of the localized
analytic category.
