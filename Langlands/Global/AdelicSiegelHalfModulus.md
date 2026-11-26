# Comparison of the Siegel modulus and the standard half modulus

`halfModulus_bot_eq_siegelSqrt` identifies the half modulus of a positive torus
point in the minimal standard parabolic with the positive square root of the
Siegel root product used by `IsSiegelPoint`.

The minimal standard parabolic and its radical represent the corresponding
dynamic subgroups of a standard cocharacter. The modular character of the
parabolic is the conjugation modulus on this radical by `adelicParabolicModulus`.
The positive-torus modulus formula in `PositiveTorusUnipotentModulus` evaluates
that same conjugation modulus by the product of the positive relative roots
with their multiplicities. Taking the square root gives the comparison.

`AdelicSiegelHalfModulusStatement` assumes nested half-modulus compatibility.
When the torus point is also the image of a positive split point of a standard
parabolic, lift that split point to the minimal parabolic. The lift and the
torus point agree in the minimal parabolic by injectivity of its inclusion
on adelic points. Compatibility identifies the half modulus of the lift
with the half modulus of the original point.

This identifies the normalizing determinant and the Siegel factor in Delorme,
*On the Spectral Theorem of Langlands* (2023), §2, p. 6, and Proposition 3.6,
equation (3.4), p. 13.
