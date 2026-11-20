# Jacquet functionals from real bottom-minor products

The coefficient functional for a column configuration is the composite of
multiplication by its bottom-minor product, a compact and Lie intertwiner
into a real principal series, and evaluation at the identity. The
decomposition into products in `RealBottomMinorProducts` shows that a
nonzero compact intertwiner has a nonzero coefficient functional. If they
all vanish, its values at the identity vanish. Compact equivariance gives
vanishing on the orthogonal group, which determines the functions.

Choose a nonzero coefficient functional with minimal column index sum.
The Lie product rule expresses its strictly upper triangular action as a
sum of terms from configurations of smaller index sum, by
`RealBottomMinorTriangular`. Those functionals vanish by minimality. The
diagonal derivative subtracts the number of appearances of each column
from the target Jacquet exponent. For a sign reflection the same count
changes the parity modulo two. This proves the real Jacquet functional
conditions on the original source of the multiplication maps.

This is an internal argument for the scalar commutant, using the
published principal-series derivative at the identity and the
compound-minor product rule.
