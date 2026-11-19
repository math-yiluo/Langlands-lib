# Descent of a normalized real principal-series vector to its bottom rows

`RealGodementRowDescentStatement` starts with the smooth position
principal series with a prepended real character `c`. Dividing a
vector by the outside determinant factor `c(det g)|det g|^(m/2)`
gives the pullback of the smooth function `normalizedOnRows`
on the domain of full-row-rank rectangles.

If two translating matrices have the same bottom rows, their left
ratio has the bottom rows of the identity. It factors as a diagonal
whose only possibly nontrivial entry is the leading one, times an
upper unipotent. Its determinant is that entry. The defining
principal-series character of the ratio is precisely the outside
determinant factor. Those factors cancel in the ratio of values,
giving equality of the normalized vectors.

The rectangular representative evaluates at the signed-cofactor
completion. The completion has positive determinant on the
full-row-rank domain, so the denominator there is its positive
determinant to the exponent of `c` plus `m/2`. The completion is
smooth, and composition with the smooth unit-chart extension of the
vector and division by that smooth nonzero power gives smoothness.
The bottom-row identity then gives the asserted pullback formula.

This is the rectangular descent used in the compact-support
Godement construction, with the last rows for the Library's upper
triangular Borel. It supplies the normalized rectangular data to
which a compactly supported test cutoff can be applied.
[Jacquet, *Archimedean Rankin–Selberg Integrals*, §7.1, p. 46](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
