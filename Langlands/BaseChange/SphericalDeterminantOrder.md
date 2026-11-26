# Support at a fixed determinant order under spherical base change

If a spherical test on the extension field has support at determinant
order `m`, `SphericalDeterminantOrderStatement` gives pointwise vanishing
of its base-change image outside determinant order `l * m`. The Satake
condition on the map is the sole hypothesis relating the two fields and
the degree. Both field universes are independent.

The proof first compares determinant twists through the map. Composing a Satake
character with the determinant twist by `z` scales its parameter by `z`.
Taking the `l`-th power of this scaled parameter gives the powered parameter
scaled by `z ^ l`. Applying Satake separation to this equality of values
proves the intertwining identity for the two twists. A function supported
at order `m` is an eigenvector of every determinant twist. The
intertwining identity therefore gives the eigenvalue of the base-changed
function. Choosing `z = 2`, injectivity of its integer powers forces the
asserted support at every point with a nonzero function value.

This is the support comparison used in Henniart–Lemaire (2011), I.6.10,
printed pp. 51–52 (PDF pp. 59–60), before removing the central averages.
The argument uses the same determinant twist as the remark after I.6.11.

Source ID `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.
