# The actual same-universe saturated fibre-product square

This internal construction forms a complete strong commutative square in
`SaturatedAtlasPresentation.{u,v,v}`, retaining the independent field and
common space/index universes. Saturation of the input presentations is part
of their object data. Smallness of the actual original pair-chart quotient
is an explicit additional premise.

`FibreProduct.smallFstHom_comp` proves equality of the entire original
compatible strong composites. Their base maps agree by the original
quotient square. On each source chart choose the underlying pair's original
common base chart. Composition then gives the original left and right
pushout legs followed by their base maps. Chart change to the original
factor chart is the identity, so the pushout algebra identity equates these
pullbacks. Coherent strong extensionality recovers all admissible pullbacks.

`geometricCompatibleMap` retains the original complete compatible map of a
saturated morphism. `smallFibreProduct` saturates the actual small atlas
presentation, preserving its space in `Type v` and its index universe `v`.
The two `smallFibreProductFst` and `smallFibreProductSnd` maps extend the
complete original strong projections to saturation and compose with the
canonical comparison isomorphisms into the original objects.

`smallFibreProduct_condition` first extends the original equality by
functoriality of saturation, then uses naturality of the actual comparison
isomorphisms. Its conclusion is equality of the complete strong morphisms,
not merely their base maps.

No categorical pullback universal property or etale assertion is proved in
this module. Smallness still needs to be supplied, for example by a
small-spectrum cover obtained from finite local models. These are further
requirements of Task 7349. No external statement is transcribed.
