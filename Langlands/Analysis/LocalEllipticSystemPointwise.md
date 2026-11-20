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
