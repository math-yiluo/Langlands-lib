# Strict uniqueness for the actual small fibre-product cone

This internal construction packages the actual same-universe saturated
square as `smallFibreProductCone` and proves strict uniqueness for every
complete strong map into it. Quotient smallness is explicit. No cone-lifting
existence or etale assertion is assumed or established here.

The exact original pair-chart image criterion survives space shrinking.
For two complete compatible strong maps from an arbitrary original source
atlas into the small atlas, choose for each source chart one target chart
admissible for the first map. Equality after the two complete projections
implies that the second map also lands in this same target chart, by that
exact image criterion. At this common target, equality of the two composite
bounded pullbacks identifies the composites with each original left and
right pushout leg. The actual affinoid pushout's algebraic hom-extensionality
therefore equates the two bounded maps into the source chart algebra. The
chart equations give equality of continuous base maps, and complete coherent
strong extensionality gives equality of the entire maps. The argument uses
bounded algebra maps; it does not infer uniqueness from ordinary projected
points, which need not distinguish fibre-product points.

For saturated sources, precompose with the source saturation comparison and
restrict to the complete original maps. Functorial saturation and canceling
the target comparison isomorphisms transfer equality after the two original
projections. Original strict uniqueness then applies. Extending and canceling
the source comparison proves `smallFibreProduct_hom_ext` as equality of the
entire saturated strong maps.

The field universe and common space/index universe are independent. The
actual cone object/projections are those already constructed in
`FibreProductSmallSquare`. A limiting property, an etale-derived small cover
and etale base change remain further requirements. No external statement is
transcribed.
