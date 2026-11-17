# Full field points on actual original-chart domains

This internal deduction identifies full field points of an actual original-chart
domain with ambient full field points whose ordinary point lies in that domain.
The base field, space, chart-index type and target field retain independent
universes. The target field needs only its normed field and normed algebra
structures. No completed-residue comparison is assumed.

Restriction retains the ambient evaluation at every original chart contained
in the domain. The chart-point realization and restriction compatibility descend
literally to the subspace atlas. Mapping this restricted field point along the
actual full strong inclusion recovers the ambient field point: a source chart
admissible for each target chart exists by full local-domain closure, and the
inclusion pullback is the original atlas restriction.

The inclusion is injective on full field points. Equal images have equal
ordinary points by the injectivity of the subspace inclusion. Each domain-chart
evaluation is recovered from the image evaluation in the corresponding ambient
chart, where the pullback is the bounded identity. These facts give
`originalDomainFieldPointEquiv`.

The provenance is the existing all-chart field-point definition, actual
subspace atlas, original-domain inclusion and full local-domain closure. This
is a supporting domain-local interface; it does not establish preservation of
general categorical pullbacks.
