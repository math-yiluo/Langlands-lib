# Principal-open ranges for scheme analytification

This internal module establishes the principal-open range input used in the
center and gluing reductions. The field and scheme range over the same arbitrary
universe, under the complete, ultrametric, nontrivially normed field and locally
finite type hypotheses of the published scheme analytification construction.

`OpenGluing.range_baseMap_of_localization` applies the affine localization range
formula to a specified algebra map. It installs the algebra structure induced by
that map and its compatible scalar tower, so the canonical tower map is the given
map.

`OpenGluing.range_localMap_basicOpen` applies that formula to the actual coordinate
restriction on a principal affine open. The localization instance comes from
`CenterRange.isLocalization_restriction_basicOpen`; the conversion from
nonvanishing to center membership is
`CenterRange.range_localMap_basicOpen_of_nonvanishing`.
`OpenGluing.basicOpenRangeData` packages these formulas as the explicit
`CenterRange.BasicOpenRangeData` proposition.

`OpenGluing.range_ι` then applies the center-range reduction: the inverse image
of an affine open under the global center is the range of its chart map. That
reduction chooses a principal neighborhood of a point's center and uses
compatibility of the quotient chart maps with restriction.

These are derived consequences of the published constructions, principal
localization, and the affine immersion comparison. This module proves no center
surjectivity, rational-fibre uniqueness, or separatedness assertion.
