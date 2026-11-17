# Represented quotients at positive weight cutoffs

This internal derived construction represents the all-test additive coordinates
from `RootWeightLayer` as an actual group-scheme homomorphism. It uses a supplied
regular root-height chart and independent nonnegative `RootWeightData`, and
reuses the pointwise Yoneda construction and coordinate projections from
`VectorCoordinateBlockQuotient`.

For every natural `d`, the source is the represented subgroup at cutoff `d + 1`.
The target is the standard vector group indexed by roots of weight exactly
`d + 1`. The target can have rank zero. `pointInLevel` maps source points into
the actual generated subgroup. Composing it with the quotient-defined additive
coordinate homomorphism gives `quotientPoints`. The coordinate formula proves
naturality on every scheme test, and `homOfPoints` gives `quotientMap`.

The coordinates of the inclusion into the original chart are the extension by
zero of the term's own affine coordinates. The exact support is a subset of
these retained coordinates. `quotientMap_hom` identifies the underlying scheme
map with the ordinary coordinate projection onto this subset, through the two
finite enumerations. These enumerations only label affine coordinates and do
not reorder any root products. The existing projection theorems then imply
flatness, surjectivity and local finite presentation of this quotient map.

The source group law is the law transferred from the actual subgroup; the
argument does not assume it is additive. Exact kernel comparison, a finite
series, and the construction and descent for actual supplied parabolics remain
separate obligations. No additional external source claim is made.
