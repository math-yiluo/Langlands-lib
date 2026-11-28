# Parabolic Haar density in relative split coordinates

The ambient norm-one Levi splits into the relative positive split
component and the intrinsic norm-one Levi. In this product the
parabolic modular density is entirely a function of the first
coordinate. For a dynamic parabolic, the existing density theorem
identifies it with the negative modulus parameter on the Levi.
The intrinsic norm-one coordinate has zero character logarithm
after the Levi inclusion, so it does not affect that parameter
power.

`relativeParabolicDensity` chooses the relative split Haar
normalization for a given ambient norm-one Levi Haar measure. It
preserves the prescribed intrinsic norm-one Haar measure. Pulling
the density back through the measure-preserving decomposition
gives a function of the first coordinate. The weighted product
formula puts that function on the split measure. The same
normalization works for every restriction of the intrinsic
coordinate, including the principal fundamental domain used in
unfolding.

This is the weighted Levi-coordinate change for the measure
in (7.7) of P. Delorme, *On the spectral theorem of Langlands*,
Advances in Mathematics 426 (2023), 109107, pp. 23–24.
