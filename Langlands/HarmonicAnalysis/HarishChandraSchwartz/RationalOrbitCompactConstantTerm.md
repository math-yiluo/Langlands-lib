# Compact fiber maps for the actual orbit constant term

`rationalOrbitCompactConstantTerm` sends a vector of the untwisted compact
picture at a given unitary parameter to the normalized constant term of its
actual coefficient at that parameter. It takes values in the sum of weak
and positive exponent spaces. `rationalOrbitCompactPositiveConstantTerm`
composes it with the positive projection. Both are complex-linear in the
compact vector. Evaluating them on a section's compact restriction gives
the original orbit constant term and its original positive part.

At a fixed unitary parameter, the inverse compact comparison extends any
compact vector to the actual induced fiber. The smooth prescribed-values
theorem realizes this vector as the value of a smooth orbit section. The
finite self-twist stabilizer premise follows from the finite discrete-series
stabilizer by `unitaryClassStabilizerEquivDiscreteSeries`. The published
`rationalOrbitConstantTermExistence` then gives the constant term of the
fiber's coefficient under the displayed standard-parabolic basis data.
The compact restriction formula identifies that coefficient with the
original orbit coefficient. This permits the linear constant-term and
positive-projection maps on the full compact fiber.

This is a derived fiberwise linearity result for making the bounds of
Waldspurger VI.2.3 uniform on a fixed section level.
