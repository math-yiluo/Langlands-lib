# Matrix coordinates for a single varying infinite place

In the actual mixed matrix coordinates, replace all coordinates of an invertible matrix except a selected real or complex place by a fixed tuple. This operation is the restriction of an affine map on the ambient matrix space. Its linear part projects onto the given place and inserts that matrix with zero at every other place.

The affine map sends a tangent direction of the form `g X` to the tangent direction at the frozen matrix for the Lie element supported at the selected place. At a standard compact point, the frozen matrix is the frozen identity multiplied by the compact element at the selected place.

Pullback by this map sends smooth functions to smooth functions and preserves real analyticity in the matrix charts. The chain rule intertwines right differentiation before the pullback with differentiation in the supported direction after restriction to the selected place.

These coordinate identities are internal to the Library's mixed adelic group and its local operator actions.
