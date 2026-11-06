# Transport of actual torus-subgroup charts

Worker 706. These internal constructions implement the base-change step in
SGA 3, Exposé XI, proof of Theorem 4.1 (registered source
`sga3-exposes-xi-xii-xiv-gille-polo-2008`, `Expo11.pdf`, PDF page 21).

`HasChartCover` is the exact existential chart-cover property for a supplied
actual group scheme, using the published definitions of `IsOpenChart` and
`CoversFieldPoints`. The range comparison lemmas use witnesses on every test
scheme: equal subgroup ranges remain equal after postcomposition, and an
ambient isomorphism also reflects equality. `familyHom_postcomp` follows from
naturality of the canonical iterated-pullback comparison.

`pushFamily` views a family over a changed base as a family over the original
base, by composing its inclusion with the canonical comparison isomorphism.
This preserves closedness. `familyHom_pushFamily` checks equality of the
actual inclusions by their projections to the original ambient group scheme
and to the test base.

The equality-of-ranges interface reuses
`SubgroupFunctor.range_comp_iso_eq_iff` from
`Langlands.GroupScheme.Rational.ParabolicAmbientTransport`, with the submitted
argument order retained.
