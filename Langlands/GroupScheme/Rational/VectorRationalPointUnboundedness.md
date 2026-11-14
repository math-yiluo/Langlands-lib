# Unbounded rational points in natural vector coordinates

This internal supporting construction represents natural vector coordinates as
actual global regular functions. The function `globalVectorCoordinate e i` is
the `i`th coordinate of the identity morphism of the vector group. Naturality
identifies its value at each rational point with that point's supplied vector
coordinate, evaluated through the spectrum global-section comparison.

The unboundedness theorem applies to any affine group scheme over a valuative
field with natural vector coordinates of positive dimension, provided some
field element is valuatively larger than one. If all rational points were
algebraically bounded, a coordinate function would have a nonzero bound `b`.
The point with coordinate `b * t`, where `1 <ᵥ t`, contradicts that bound.
No finite-type, completeness, henselianity or characteristic restriction is
used. This is a direct consequence of the published regular-function definition
of algebraic boundedness and natural vector coordinates, and is not attributed
to a separate literature theorem.
