# Strong representatives of domain–étale factorizations

A strong morphism with a localized domain–étale factorization has a
strong representative of that factorization on a common source
refinement. `RefinedDomainEtaleFactorization` stores the strongly étale
envelope over the original target, an analytic domain in the envelope,
and a presentation equipped with strong quasi-isomorphisms to the
original source and to the envelope domain. Its square is an equality
of strong morphisms to the original target.

`refinedDomainEtaleFactorization` uses a right fraction for the étale
morphism. The numerator is strongly étale since its localized map is the
denominator isomorphism followed by the original étale morphism. The
domain is transported by inverse image along the denominator isomorphism.
The resulting isomorphism from the original source to the transported
domain has a right fraction with two quasi-isomorphic legs. The two
strong composites agree in the localization. The localization equality
criterion gives a further source refinement on which they agree as
strong morphisms.

The provenance is internal. The construction uses the published
localized étale criterion, domain transport and the calculus of
right fractions for saturated presentations.
