# Haar measure in split coordinates

`splitGLCoordinates` identifies matrices over the split algebra with tuples of
matrices, then passes to units. The matrix equivalence and its inverse are
continuous because each output entry is an input coordinate. In these coordinates
base change is diagonal and the entrywise automorphism shifts the coordinates.

`splitProductMeasure` transports the finite product of the given Haar measure to
the group over the split algebra. The integral of a split tensor factors by the
finite-product integral formula. Haar uniqueness gives a scalar between any two
Haar measures on this group. Evaluating the split-tensor identity on the indicators
of a compact open subgroup fixes that scalar at one. This proves that every Haar
measure with the required normalization has the same product coordinates.

This is a proof component of `SplitMatchingStatement`. The normalization is
the product measure of Henniart–Lemaire (2011), II.2.15, and the split coordinates
are those of Arthur–Clozel (1989), Chapter 1, §5.
