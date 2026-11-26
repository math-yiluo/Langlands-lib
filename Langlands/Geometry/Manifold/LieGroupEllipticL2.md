# Local Haar $L^2$ control for elliptic word equations

`exists_lieWord_l2_evaluation` gives a compact set and a finite constant that bound evaluation at the identity of every smooth solution of a single positive-order elliptic left-invariant word equation. The bound is by the Haar $L^2$ norm on the compact set. The equation is specified by its homogeneous top-order words and shorter words, and its symbol must be nonzero on nonzero real covectors.

The coordinate word operator in the Euclidean identity chart has smooth coefficients and the required principal symbol at the chart point. Restrict to a coordinate ball on which chart volume is bounded by a finite multiple of Haar measure. The positive-order local interior estimate on that ball controls the order-zero derivative at its centre by the Lebesgue $L^2$ norm on a smaller closed ball. Its norm is bounded by the norm on the larger closed ball. Push that measure through the inverse chart and restrict Haar to the compact image. The resulting norm bound has the square root of the measure comparison factor, and the chart centre represents the group identity.

This is an internal composition of `exists_lieWordCoordinateOperator`, `exists_chartVolume_le_smul_haar` and `exists_localElliptic_interior_derivative_l2_bounds`.
