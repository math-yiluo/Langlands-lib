# Original quotient recovery on actual cover components

This internal Task 7200 adapter records the actual disjoint free presentation
of the constructed layer module with its unchanged component ranks. It also
constructs the isomorphism from the actual global quotient restricted to one
original chart to that chart's original vector quotient. The actual module
and group comparisons are the existing prescribed pullback comparisons.

`globalFaceQuotientComponentIso_projection` proves the exact original quotient
square: the pulled-back global quotient projection followed by the component
comparison is the actual global-term chart comparison followed by the original
local vector quotient projection. Its proof uses canonical pullback naturality,
the actual global cover recovery, and the original component projection and
term comparison equations.

The final theorem applies the constructed module overlap datum, effective
module descent and scalar locality to the actual global quotient. Its sole
extra comparison premise is equality of the original scalar operations on
common literal affine component parameters. No module cocycle, effectivity
premise or vector-bundle representer is supplied.

The provenance is derived from the actual finite face cover, global full
quotient, cover-module construction and proved actual module descent. The
quotient-specific affine scalar comparison remains a consumer obligation.
