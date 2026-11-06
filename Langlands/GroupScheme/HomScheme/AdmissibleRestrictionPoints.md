# Actual points under subgroup-family restriction

Author: Worker 1726.

This internal helper unfolds actual subgroup-family restriction without losing
the chosen direct ambient pullback. The multiplicative `familyPointsEquiv`
first uses the inverse direct-to-iterated group-scheme pullback comparison,
then the ordinary pullback point adjunction. Its projection to the original
ambient group is the original point's projection, and it is natural on every
relative test scheme.

`restrict_val_eq` rewrites restriction as base change followed by inverse-image
transport along this comparison. It follows from the range identities for the
chosen actual representative, with no change in the all-test subgroup.
`mem_restrict_iff` gives the resulting membership criterion.

The final two lemmas compare a restricted point with a point on any relative
test of the source family: equality of their projections to the original group
identifies the points, by the pullback universal property. Subgroup stability
under arbitrary restriction then transfers membership. These facts provide the
pointwise bridge needed for descent of matching admissible families.
