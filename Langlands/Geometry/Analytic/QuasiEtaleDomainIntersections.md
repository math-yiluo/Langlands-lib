# Actual intersections of compact quasi-étale domain charts

The general domain constructions work over a complete ultrametric normed
field, with independent field, space and chart universes. The factorization
and quasi-étale-site constructions use equal space and chart universes.

`domainOrderMap` realizes inclusion of two ambient analytic domains by an
actual localized analytic arrow, with its full ambient-inclusion triangle.
`domainIntersectionCone` realizes their meet and its two projections.
`domainIntersectionIsLimit` proves that this is a categorical pullback
against every localized analytic test object. The universal arrow is obtained
from the actual domain factorization API. Its image lies in both domains by
the supplied equality of the two ambient arrows. Monicity of actual domain
inclusions proves both projection equations and uniqueness.

`HasDomainEtaleFactorization.of_domain_le` shows that any smaller ambient
domain inherits a domain-étale factorization of the larger domain's map to
the base. It restricts to the smaller domain viewed inside the larger one,
then uses the actual nested-domain isomorphism and its inclusion triangle
to return to the smaller domain in the ambient space. This is inheritance
of an existing envelope; no global envelope for an arbitrary quasi-étale
map is assumed.

For `FiniteCompactDomainChartCover`, each selected ambient domain is compact
and Hausdorff through its stored isomorphism to the compact chart source.
`intersectionDomain i s` is the meet of the domain at `i` with the domains
in the finite set `s`. This description includes an anchor even if `s` is
empty. Its map to the base inherits the anchor's domain-étale factorization,
and `intersectionObj` is therefore an actual quasi-étale site object.

When the ambient object's underlying space is Hausdorff, each selected
domain is closed. Finite induction shows that the meet over `s` is closed;
its intersection with the compact anchor is compact. Thus the constructed
intersection object is compact Hausdorff under precisely that additional
ambient Hausdorff hypothesis.

This is an internal consequence of the proved domain-factorization,
nested-domain and finite compact domain-chart APIs, using ordinary compact
Hausdorff topology. It supplies actual pullbacks of domain inclusions and
compact quasi-étale finite intersections. It does not construct compatible
group-action lifts or presentations for all higher terms of arbitrary
lifted covers, and does not prove the global comparison theorem.
