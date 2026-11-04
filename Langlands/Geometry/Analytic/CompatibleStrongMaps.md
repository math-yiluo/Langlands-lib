# Strong atlas maps with explicit local affinoid compatibility

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
Definition 1.2.7, printed p. 18 (zero-based PDF index 14), defines a
strong morphism by a continuous map, a containing target chart for every
original source chart, and compatible morphisms of affinoid spaces for all
admissible original chart pairs. Proposition 1.2.8 on the same page extends
this compatible family uniquely to both enlarged atlases. The registered
source is `berkovich-1993-etale-cohomology`, PDF SHA-256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

This implementation makes the local compatibility requirement explicit.
`StrongHom.HasLocallyCompatiblePullbacks` requires the original bounded
pullbacks from each source chart into any two admissible original target
charts to agree on the actual source inverse-image domain of every common
original target subchart. Agreement is the complete bounded algebra
equation of `IsLocalMapChartChange`; the inverse-image domain uses the
constructed full affinoid pushout quotient. The original `StrongHom`
restriction equations also remain required.

`CompatibleStrongHom` contains this continuous map, target existence, every
original admissible bounded map, its ambient equation, both original
restriction equations, and the explicit local compatibility law. It
assumes no enlarged morphism or extension output. The source does not
separately spell out the word “compatible”; the law here states the local
morphism agreement on actual affinoid inverse images. The internal results
below establish its consequences and its equivalence with the previously
formalized coefficient-test law. No claim is made that the weaker
`StrongHom.restriction_comm` alone supplies this compatibility.

`hasLocallyCompatiblePullbacks_iff` proves equivalence with
`HasCoherentPullbacks`, by the full-domain factorization theorem
`isMapChartChange_iff_local`. The compatibility also compares different
original source charts: on any actual local source domain `W` included in
both, `original_pullback_restrict` identifies the restricted original
bounded maps with the constructed maps on `W`.
`original_pullbacks_local_overlap` then proves their local compatibility
through every common original target subchart. The source parent charts
need not be comparable. This uses full bounded-map naturality and
coefficient compatibility, rather than equality on spectrum points.

Identities have compatible original restrictions, and every strong map
with saturated source supplies an instance. For every
`CompatibleStrongHom`, `saturationExtension` constructs the actual strong
map on the two enlarged presentations, with the same continuous map.
`saturationExtension_recovers` retains every original bounded pullback.
The uniqueness and unique-existence results range over all strong maps
on the two enlarged atlases and require recovery of all original bounded
maps, including information invisible on spectrum points.

The explicit compatibility convention is motivated by Definition 1.2.7.
Its equivalence with the coefficient-test law, its compatibility on
arbitrary actual source-domain overlaps, and the extension's construction
and uniqueness are implemented internal consequences of the previously
constructed full affinoid domains, bounded chart change and saturation.
Composition and the analytic category comparison are subsequent work.
