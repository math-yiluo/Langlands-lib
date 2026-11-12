# Diagonalization retaining an actual coordinate eigenline

This internal derived construction combines the actual coordinate-line
character, the integer classification of algebraic characters of the
multiplicative group, and the prescribed-vector split-torus eigenbasis.

`HasCoordinatePowerAction sigma j m` states that every point of the
multiplicative group over every coefficient algebra acts on the selected
coordinate vector by the m-th power of that point's unit. The integer
`coordinateLineCocharacterWeight` is obtained by applying `gmEndEquiv` to the
actual algebraic character on the stabilized coordinate line.

The universal character-space equation for that coordinate vector gives the
same equation over every coefficient algebra. The actual character equals the
power map of its integer, proving the power-action predicate.

Transport along the published isomorphism from the multiplicative group to
the one-dimensional split torus makes this coordinate vector a universal
exponent vector with the same integer. The prescribed-vector eigenbasis
construction gives an invertible rational matrix B with the original
coordinate vector as its selected column, and with its prescribed exponent
at that column. Conjugation by B inverse diagonalizes the original
cocharacter. Equality of actual homomorphisms follows by checking the
universal Laurent point using the all-algebra diagonalization equation.

The resulting diagonal weight at the selected column is exactly the integer
of the original algebraic line character. The construction does not yet
transport a larger subgroup's line stabilizer through this change of
coordinates or establish a height estimate.
