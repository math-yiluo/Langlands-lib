# Complex Godement sections

`godementSection` is the rank-raising integral of Jacquet's equation (7.1) in
upper-Borel coordinates. The input of rank `m` has list `ds` and the output
has list `d :: ds`. To compare with Jacquet's lower-Borel formula, apply the
long Weyl element on the left in both ranks, and change the integration
variable from `h` to `h w_m`. This turns `[h, 0]` into `[0, h]` after multiplying
by the long Weyl element in rank `m + 1`. The determinants of the two Weyl
elements contribute the constant `d.character ((-1)^m)`, which can be included
in the test function. `normPower` takes a complex power of the squared complex
norm, and `characterWeight` multiplies that power by the specified character.
`godementSectionIntegrand` is the integrand in the smaller general linear group.

`godementSection_covariant` proves the Borel transformation law. Multiplying
`g` on the left by a diagonal times an upper unipotent acts on its trailing
rows by the trailing diagonal times the trailing upper unipotent. Right
translation by that smaller matrix in the integral moves the action to the
input vector and the determinant character. The quotient of the determinant
powers contributes a shift of `-1/2` at every trailing diagonal position,
which gives the larger principal-series character. The covariance uses the
right invariance of the measure and the proved Borel law of the input vector.
Absolute integrability and smoothness of the section require further results.

[Jacquet, *Archimedean Rankin–Selberg integrals*, §7.1, equation (7.1) and Proposition 7.1 (iv), p. 43](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
