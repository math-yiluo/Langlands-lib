# Actual quotient chart and determinant density for the intermediate tail

Worker 318 constructs consumer data for the intermediate-rank JPSS comparison.
The constructions use published definitions and the published lower-block
quotient chart. They assert no disintegration or integration identity.

`quotientChart n d` has domain the product of the actual quotient
`N_(n+1) \ GL_(n+1)`, the rectangular matrices with `d` rows and `n+1`
columns, and the actual lower-triangular subgroup of rank `d`. Its codomain
is the actual JPSS quotient of index `n+d`. It composes the published
lower-block chart with the published quotient homeomorphism for the numerical
equality `(n+1)+d = (n+d)+1`. The representative formula displays exactly
that numerical matrix reindexing. Injectivity and continuity follow by
composition from the published chart and that homeomorphism. These laws
make no claim that the chart has full or conull range.

`quotientDensity abv n d` is the extended nonnegative real function
`ofReal (quotientDeterminantAbs abv n q ^ (-d))`. The published determinant
absolute value is invariant on the actual quotient and is strictly positive
because its representatives are invertible. Consequently this density is
strictly positive and finite. Its real value is exactly the real determinant
norm raised to the integer power `-d`, and it also equals the integer power
of the extended nonnegative real determinant norm.

For a continuous absolute value over a topological field, continuity of the
determinant norm descends through the actual open quotient map. Continuity
of integer powers away from zero and of `ofReal` proves continuity of the
density. With a Borel measurable structure on the small quotient, this
also proves its measurability. The result retains any field universe, both
rank indices including zero, and the specified absolute value; it does not
select any Haar measure or normalization.

The provenance is internal composition and elementary consequences of the
published lower-block quotient and determinant-norm constructions. The
density is the one needed for the comparison motivated by JPSS section 9.3;
no external theorem about quotient measures is asserted here.
