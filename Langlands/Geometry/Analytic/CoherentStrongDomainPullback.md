# Constructed strong pullbacks on source local domains

For original strong-map data `f : StrongHom A B`, `localChartPullback` constructs
an actual bounded map from every containing original target chart algebra to
the algebra of any full local domain of `A`. It restricts the supplied pullback
for a target chosen for the domain's original parent chart, then uses the
finite-cover target-chart-change construction. Neither atlas is assumed
saturated or directed.

The ambient chart equation is proved for the constructed map. Any further
target-chart change gives the direct constructed map. Consequently the
constructed local family satisfies the full `IsMapChartChange` law for arbitrary
presented-affinoid coefficient tests.

The remaining two results explicitly assume `f.HasCoherentPullbacks`, a law on
the original supplied maps. For any target chart containing the whole original
parent chart's image, the constructed map recovers the original pullback
followed by the local domain's original base map. Every actual inclusion of
source local domains also commutes with the constructed maps to a fixed
original target chart.

For this source naturality, the universal domain-restriction law supplies
compatibility of the two original parent-chart structural maps. Preservation
under the coherent original strong map gives the corresponding target law.
Composing with the target change and applying its bounded-map uniqueness
identifies the complete maps. No equality of bounded maps is inferred from
equality on spectrum points.

This is internal provenance from the existing finite-cover chart-change,
universal domain-restriction and intrinsic-coherence constructions. It builds
the local maps without assuming their extension as input. It does not yet
construct a map into a target local domain or the strong map between enlarged
atlases, and does not assert coherence of every arbitrary original `StrongHom`.
