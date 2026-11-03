# Scalar extension from natural finite Lie coordinates

This is an internal consequence of the published `Lie.FiniteCoordinates` interface. For an affine group scheme over a commutative ring with natural finite coordinates, `scalarExtension` identifies the tensor product of the base Lie kernel with the actual Lie kernel over every test algebra. No finite-type hypothesis is used.

The construction extends the coordinate linear equivalence to the tensor product, identifies the tensor product of a finite function module with the corresponding function module over the test algebra, and uses the inverse test-algebra coordinate map. Naturality of the supplied coordinates proves that a pure tensor maps to its scalar times the actual image of the base Lie vector. Consequently `baseChangeBasis` extends any base-ring basis to a basis of the actual test-algebra Lie kernel with exactly those coefficient-change values.
