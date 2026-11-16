# Finite compact domain charts with retained étale envelopes

This internal construction works over a complete ultrametric normed field, with
the equal space and chart-index universes of the existing quasi-étale site.

The local and finite chart-selection results retain
`HasDomainEtaleFactorization` for each chosen chart's map to the base.
The local result reads the actual affinoid-domain embedding and étale arrow
from the quasi-étale condition. The finite result uses compactness to select
finitely many of its finite neighborhood families and then their chart indices.
The selected chart ranges cover the entire strong source.

`FiniteCompactDomainChartCover U` extends `FiniteCompactChartCover U`.
It retains the finite index type, actual quasi-étale site objects and over-arrows,
compact Hausdorff sources, full surjective source charts, and joint point
surjectivity. For each arrow it also stores an actual analytic domain of `U`,
an isomorphism from the selected source to that domain, and the complete
analytic-arrow triangle with the domain inclusion. Each selected source's map
to the base admits a domain-étale factorization.

Consequently each cover arrow is an analytic-domain embedding. Transport
through the stored source isomorphism gives a domain-étale factorization for
the ambient domain's map to the base. Restriction to any further source domain
preserves that factorization by the proved domain-restriction lemma.
The inherited presieve belongs to the actual quasi-étale precoverage and its
generated sieve covers, by the existing `FiniteCompactChartCover` results.

For every quasi-étale site object whose underlying space is compact,
`exists_finiteCompactDomainChartCover` constructs these data. A strong
quasi-étale representative and its source isomorphism transport compactness
to the strong source. The finite selection retains each étale envelope.
Postcomposition with the representative's target isomorphism preserves it and
makes the selected sources actual quasi-étale objects over the original base.
The cover arrows are chart inclusions followed by the source isomorphism.
Their ambient domains are literal inverse images under its inverse;
`domainImageIso` supplies the required isomorphisms and inclusion triangles.
Source-isomorphism surjectivity transports the chart-range covering property.

The provenance is internal: these are strengthened witness constructions from
the existing local quasi-étale condition, compactness, and the proved domain and
isomorphism APIs. They assert neither a single global étale envelope for every
quasi-étale map, nor membership in an arbitrary supplied covering sieve.
Compatible group-action lifts, finite presentations of higher Čech terms,
and the global cohomological comparison remain further obligations.
