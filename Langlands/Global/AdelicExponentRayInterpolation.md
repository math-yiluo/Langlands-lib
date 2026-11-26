# Uniform bounds for an exponent component on a split ray

Fix an unnormalized generalized exponent, one positive split point and a set of starting points.
Suppose that at each fixed integer position on its ray the norm of the component is bounded by
a constant times a common nonnegative function of the starting point. The theorem
`exists_rayBound_of_exponent_samples` bounds the entire ray by that common function times the
absolute character power and a polynomial in the ray parameter. The degree and constant are
uniform in the starting point. Any rate strictly above the norm of the unnormalized character
at the ray point then gives a pure exponential bound by `exists_rayBound_with_larger_rate`.
This latter assertion is recorded as `AdelicExponentRayInterpolationStatement` and proved
by `adelicExponentRayInterpolation`.

The polynomial orbit gives one degree bound, and restriction to the chosen line is an ordinary
complex polynomial. Lagrange interpolation on the first consecutive integer nodes uses only
finitely many of the hypothesized bounds. The sum of the absolute coefficients of each fixed
Lagrange basis polynomial bounds its growth. A polynomial times a geometric sequence of ratio
less than one is bounded, which permits increasing the exponential rate.

The finite sampling argument is a single-exponent, one-dimensional version of the
exponential-polynomial estimates in Mœglin–Waldspurger, *Spectral Decomposition and
Eisenstein Series* (1995), I.4.2, pp. 51–54. The split-ray setting comes from the growth
argument in Delorme, *On the Spectral Theorem of Langlands* (2023), Proposition 3.6,
equation (3.4), pp. 13–14. The bound here assumes fixed-position estimates for one
component and quantifies uniformly in the starting point.
