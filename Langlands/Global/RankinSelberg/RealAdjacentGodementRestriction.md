# The restricted real Godement coefficient

This internal comparison derives the restriction kernel in Jacquet,
*Archimedean Rankin–Selberg integrals* (2009), §8.3, p. 58 (the formula for
`W(diag(g,1))` before (8.3)), starting from the Library's actual
`godementColumnValue`. The Library uses a free **first** column before
undoing its Weyl reversal, and the positive Fourier kernel of the supplied
parameter. The resulting row test is `realFourierTransform a f`, with the
self-dual measure already used by the first-column formula.

Write `m = r+1`, and `w_j` for the Library long Weyl element of size `j`.
`realAdjacentGodementCoefficient` evaluates `godementColumnValue` at
`w_(m+1) * g`, the coordinate used by `realGodementSchwartzJoint` for the
original upper coefficient. For any Schwartz rectangle test `Φ` satisfying
`Φ([A | x]) = F(A) f(x)`, `realAdjacentGodementRestriction` expresses the
restriction of this actual function to `diag(g,1)` as the integral of
`realAdjacentRestrictionKernel` times `realAdjacentWeylSign r c`. This
constant is the actual determinant character at `w_(m+1)` times its value
at `w_m`; it is not dropped or included in the Haar measure.

In the lower group integral change the column translator `h` to `k⁻¹ w_m`.
The supplied lower Haar is invariant under inversion and right translation.
The lower coefficient is then evaluated at `k`, and the Fourier frequency
`(h⁻¹)ᵀ e₁` becomes the last row of `k`. Multiplying `[x | h]` on the right
by `w_(m+1)` makes `[h w_m | x]`; subsequent padding by `g` replaces the
square block by `k⁻¹ g` and leaves the last column unchanged. The separated
test therefore pulls the square factor out of the free-column integral.
The determinant powers are unchanged by either Weyl element, while the
ordinary determinant characters give the two stated constants.

The equality uses the total integral convention, needs only the pointwise
separation identity, and makes no convergence or model membership claim
for arbitrary `U`, `F` or `f`. It does not prove that these coefficients
span the prescribed uniform model, identify a dual separated test, or
prove analytic continuation or a functional equation.
