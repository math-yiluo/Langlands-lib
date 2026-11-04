# Constructed strong pullbacks between local full domains

For an arbitrary original strong atlas map `f`, a source local full domain `U`
and a target local full domain `V` containing its ambient image,
`localDomainPullback` constructs a bounded algebra map from the actual unchanged
algebra of `V` to the actual unchanged algebra of `U`. The parent-chart map is
`localChartPullback`. Its spectrum lands in `V.domain.locus`, by the ambient
equation and injectivity of the original target chart. The full representation
property of `V.domain`, tested on `U.algebra`, supplies the factorization.

`localDomainPullback_comp_baseMap` is an equality of complete bounded maps.
`localDomainPullback_unique` uses the full representation property to cancel the
target structural map. `localDomainPullback_ambient` recovers the original
continuous ambient map on spectra. Map uniqueness does not use equality of
spectrum maps.

`localDomainPullback_comp_chart` identifies the composite with the target
restriction from every containing original chart. The universal domain chart
change law is preserved under the constructed bounded coefficient map. Its
uniqueness and the transitivity of the constructed local-chart family identify
the composite with `localChartPullback` to that chart.

`localDomainPullback_target` follows by full-domain cancellation and this
all-containing-chart structural equation. It needs no coherence hypothesis on
`f`. `localDomainPullback_source` uses the previously proved source naturality
of `localChartPullback` under `f.HasCoherentPullbacks`, then full-domain
cancellation. `localDomainPullback_naturality` combines the source and target
equations for every pair of local-domain inclusions. The coherence premise is a
law on the original supplied pullbacks, with all presented-affinoid coefficient
tests, and contains no extension output. Neither atlas needs saturation or
directedness.

These are internal constructions and consequences of full-domain representation,
the actual local-domain category and bounded chart change. They prepare an
extension to enlarged atlases; this file does not assert that every arbitrary
original strong map satisfies the intrinsic coherence law or identify that law
with an external definition of compatibility.
