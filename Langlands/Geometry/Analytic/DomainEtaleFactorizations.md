# Domain embeddings and their étale factorizations

This internal construction retains explicit domain and étale factorization
data for use with intersections of selected quasi-étale charts. The field is a
complete ultrametric normed field. Domain embeddings allow separate space and
chart universes; étale factorizations use the existing site's equal universes.

`domainNestedLocalizationIso` transports the proved source-category
isomorphism between a nested analytic domain and its ambient-image domain
through the comparison functor. Its inclusion triangle is the image of the
proved source-category triangle. `domainImageIso` uses the inverse-image
domain construction to transport a domain through an isomorphism, with its
actual inclusion triangle.

`IsAnalyticDomainEmbedding j` means that `j` is a source isomorphism followed
by the inclusion of an actual analytic domain of its target. Canonical domain
inclusions and the existing affinoid-domain embeddings satisfy this
property. To restrict the source of such an embedding, transport the source
domain through its source isomorphism and then flatten the resulting nested
domain by `domainNestedLocalizationIso`. The two inclusion triangles prove
the required equality. This also proves closure under composition of domain
embeddings and under source isomorphisms.

`HasDomainEtaleFactorization f` means that `f` is an analytic-domain
embedding followed by an étale arrow. It implies the existing `quasiEtale`
property by the proved domain-inclusion composite theorem and
source-isomorphism invariance. It is preserved by further source-domain
restriction and by source or target isomorphisms. Restriction uses the proved
closure of domain embeddings; target transport uses isomorphism invariance
of `etale`.

The factorization property is additional explicit information. No assertion
is made that every quasi-étale morphism has one such global factorization.
General quasi-étale composition or base change, arbitrary covering-sieve
refinements, finite nerve presentations, and the cohomological comparison
remain separate obligations. No new original-literature claim or unproved
Library proposition is used.
