# Coordinate derivatives in an invariant frame

For a smooth map from an open subset of the model space to a finite-dimensional Lie group, `exists_invariantDerivativeExpansion` expresses the derivative of the pullback of a smooth complex function in terms of its invariant directional derivatives.

The proof differentiates the local coordinate expression of left division along its second variable. Smoothness of left division gives smooth coefficients for the coordinate frame. The chain rule and a finite basis of the model space express the derivative using those coefficients. `identityChartLieDirection` maps each basis vector into the Lie algebra by the derivative of the inverse chart at the identity. This derived calculus result is used to pass to limits of functions whose invariant derivatives converge locally uniformly.
