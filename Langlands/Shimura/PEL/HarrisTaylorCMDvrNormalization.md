# Reflection of the normalized Harris conditions over a DVR

For an abelian scheme over a domain and its actual rational algebra action,
`harrisTaylorCMDvrNormalization` reflects the normalized Harris determinant
and prescribed geometric dimension from the actual generic fibre.
`extendDvrNormalizedAction` applies this to the unique extension of a
rational action on the generic fibre of a given good model over a DVR.

The fraction-field morphism is quasi-compact and dominant with reduced
base. It is scheme-theoretically dominant, so its map on sections is
injective for every chart open. Rational Lie base-change naturality
identifies the pullback of the determinant on each given finite Lie chart
with the determinant in the pulled-back chart. The same section map
transports the normalized CM coefficient polynomial since the structure
map to the CM field composes with the fraction-field map. Coefficientwise
injectivity then reflects their equality.

The good model has connected total space because the domain spectrum is
connected and the structure map is smooth with geometrically connected
fibres. Smoothness and connectedness give a single geometric relative
dimension. Its restriction to the nonempty generic fibre agrees with the
prescribed dimension by uniqueness over a field. The published comparison
with the normalized numerical test recovers the central trace from the
determinant.

This is a derived application of the Library's Lie base change, normalized
coefficient formula and relative-dimension results, with Mathlib's
scheme-theoretic dominance criterion for the maps on sections.
