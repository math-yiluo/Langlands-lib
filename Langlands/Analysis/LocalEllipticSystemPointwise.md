# Pointwise derivatives of a finite elliptic system

The theorem `exists_localEllipticSystem_derivative_bounds` converts the
weighted \(L^2\) estimate for a fixed finite elliptic system into a bound on
each Fréchet derivative at the center. It is an internal consequence of
`exists_localEllipticSystem_weighted_bounds` and the Library's averaged
Taylor estimate in `LocalSobolevPointwise`.

A uniform pointwise bound on the derivatives of orders less than \(r\)
controls the initial weighted seminorms by finite volume and the
comparison of the basis-word and operator norms. Restricting to the ball
of half the radius removes the weights, with a factor depending only on
the radius and the order. The averaged Taylor estimate then bounds the
derivative at the center by finitely many of these \(L^2\) bounds. Every
constant is independent of the solution family and of its initial bound.

## Public auxiliary lemmas

Two steps of this proof are public so that other estimates can use them:

- `derivWordNorm_le_opNorm_times_card`: at every point, the ordered word norm
  `derivWordNorm m u x` of the `m`-th derivative is at most `d ^ m` times the
  operator norm `‖iteratedFDeriv ℝ m u x‖`. Each of the `d ^ m` basis-word
  evaluations is at most the operator norm, and the square root of a sum of
  squares is at most the sum.
- `eLpNorm_half_ball_le_weightedDerivative`: for `R > 0` and `u` smooth on
  `ball x₀ R`, the \(L^2\) norm of `iteratedFDeriv ℝ m u` on `ball x₀ (R / 2)`
  is at most `(R - R / 2) ^ m` inverted (in `ℝ≥0∞`) times the weighted
  seminorm `ballWeightedSeminorm (derivWordNorm m u) x₀ R m`. The operator norm
  is at most the word norm, and the inner radius `R / 2` is one of the radii in
  the supremum that defines the weighted seminorm.
