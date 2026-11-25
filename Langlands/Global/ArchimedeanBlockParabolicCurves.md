# Local parabolic curves through the identity

`parabolicLine` takes an upper triangular matrix direction over a real or complex field. On the open set where the affine line through the identity is invertible, it gives a point of the given block parabolic. The curve uses the identity elsewhere. Invertibility holds near zero, so the curve passes through the identity and has the prescribed matrix tangent.

`localDiagonalBlock` takes a diagonal block by a continuous real linear map. `leviProjection_hasDerivAt` applies this map to the tangent of any parabolic curve. It gives the precise block tangents needed to compare the derivative of normalized evaluation with the block Lie operators.

This is an internal construction for the Lie-action comparison toward `CuspidalIsobaricAutomorphyStatement` (automorphy of isobaric sums of cuspidal representations at every place). Getz and Hahn (2024), §4.4, Definition 4.4.6, give the compact and Lie differentiation setting. The proof uses openness of the matrix units and the Library's block parabolic.
