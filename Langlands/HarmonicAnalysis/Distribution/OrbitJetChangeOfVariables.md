# Change of orbit variables for leading normal jets

Consider an open partial homeomorphism of `((O × Z) × N)` whose two directions are smooth and preserve each zero-normal orbit fiber. A weighted leading normal jet can be expressed in target orbit coordinates by composing the multilinear form with the normal derivative at the inverse point. The scalar factor is the original weight divided by the absolute orbit Jacobian at that point. This operator-valued kernel is jointly smooth on the zero-normal target when the original weight is smooth, since the orbit determinant there is nonzero at the inverse point.

For an additive Haar measure in the finite-dimensional orbit coordinate, substitution by the induced orbit chart equates the target fiber integral of this kernel against a scalar orbit function with the weighted pullback integral on the source fiber. The change-of-variables Jacobian cancels the denominator, leaving the original weight and the pulled-back normal derivative. Both sides use Mathlib's Bochner integral convention.

This internal identity will be applied with the full chart Jacobian as the original weight.
