# Ordered block exponents for normalized principal series

For ordered block sizes \(n_i\), `blockHalfExponent` is half the difference
between the sum of later sizes and the sum of earlier sizes. The proof
identifies the earlier sum with the starting position \(a_i\) of block \(i\).
For total rank \(N\) the exponent is consequently \((N-n_i)/2-a_i\).

For positive block determinant norms \(D_i\), regrouping the pairwise
ratios \(D_i^{n_j}/D_j^{n_i}\) produces one power for each \(D_i\). The
proof switches the indices in the denominator product and combines the
exponents. Taking the positive square root yields the product with the
exponents `blockHalfExponent`.

Suppose the full position characters agree block by block with the local
position characters. `principalSeriesCharacter_eq_outerHalf_mul_inner`
identifies the normalized full torus character with the product of the
normalized inner characters times the positive square root of the outer
block modulus. Here `blockDiagonalAbs` uses the determinant of the actual
diagonal matrix of a block, with norm raised to the real dimension of
the scalar field. In the proof the difference of the full and local
principal-series exponents is precisely `blockHalfExponent`. Regrouping
the positive diagonal norms inside the block gives its determinant norm.
The same proof applies to real and complex scalar fields.

This is an internal comparison of the principal-series character in
[`StandardModule`](StandardModule.md) with the ordered block coordinates
in [`RealLeviChartIntegralStatement`](RealLeviChartIntegralStatement.md).
It gives the torus normalization used in induction in stages.
