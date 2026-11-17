# Compact torus bounds for actual padded cuspidal Whittaker functions

This internal helper specializes the compact-uniform diagonal Whittaker
estimate to the actual vectors of a cuspidal operator realization. It uses
the inverse diagonal conjugation Haar modulus from
`AdelicSimpleRootGaugeHaarModulus`.

`paddedCuspWhittakerNormWeight` is the exact nonnegative function evaluated at
quotient representatives in `PadWhittakerGaugeBound`. Its measurability
follows from measurability of the cuspidal Whittaker coefficient, continuity
of padding, and measurability of the real determinant power. Its left
unipotent invariance follows from the published norm invariance of the padded
Whittaker coefficient and unipotent invariance of the determinant norm.

For a common determinant exponent `beta` of the realization, the final theorem
uses its realized cusp space and published Whittaker decay class. The compact
torus estimate applies with root exponents `-((j+1)*(t-j))`. Their sum of
absolute values is the sum of the corresponding nonnegative multiplicities.
The exact inverse Haar weight rewrites as this root-power product; commuting
the nonnegative factors gives a finite bound uniform over each compact set
of right translates.

The condition is
`beta + sigma > 3 + sum_j (j+1)*(t-j)`.
It is independent of the compact set, standard additive character and vector.
The result is derived from the named imports and does not yet compare the
torus integral with the Whittaker quotient integral.
