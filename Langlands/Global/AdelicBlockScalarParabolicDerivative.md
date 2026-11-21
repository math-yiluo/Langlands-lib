# Differentiating a scalar section along an infinite parabolic curve

For a smooth compact-finite scalar section, `hasDerivAt_smoothScalarSection_curve` evaluates the actual section differential on any curve in a fixed finite slice with the required right matrix tangent. It uses the smooth coordinates of the genuine infinite adelic group.

`normalizedCoefficient` is the scalar Levi coefficient at a compact point. At a compact point with infinite coordinate one, `normalizedCoefficient_differential_parabolic` computes its derivative along an infinite parabolic curve through the identity. The normalized scalar covariance formula gives the varying half character multiplied by the coefficient at the translated Levi point. The derivative of the latter is `coefficientDifferential`, which sums the genuine block Lie operators. The half character equals one at the identity, so the product rule gives the half-character derivative times the original coefficient plus that block differential.

This is an internal differential calculation for the normalized scalar sections of §10.1 in Getz and Hahn (2024), pp. 270–271 (PDF 282–283). The formula uses the specified parabolic curve and its half-character derivative.
