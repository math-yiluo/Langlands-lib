# Real Godement sections in the upper triangular Borel convention

`RealGodementSectionStatement` takes a smooth position principal-series
vector `f` on `GL_m(ℝ)`, an actual leading real character `c`, and a
smooth rectangular test function with compact full-row-rank support.
The lower-rank measure is Borel, finite on compact sets, and right
invariant. The section on `GL_(m+1)(ℝ)` belongs to the smooth position
principal series of the list with `c` prepended.

The section multiplies the inner integral by `c(det g)` and the
absolute determinant power `m/2`. The kernel evaluates the rectangular
test at `(0,h)g` and the lower vector at `h⁻¹`. Its determinant
multiplier in `h` is `c(det h)` times the absolute determinant power
`(m+1)/2`. The previously proved compact-support smoothness of the
inner integral and the signed-power formula for the outside
determinant factor give smoothness of the section.

In the upper triangular Borel, the last `m` rows of `b g` come
from applying the trailing block `t` of `b` to the last rows of `g`.
The proof changes the lower integration variable from `h` to `h t`
by right invariance. Since `h⁻¹ = t (h t)⁻¹`, lower-rank covariance
contributes the lower principal-series character. The outside
determinant of `b` is the product of its first diagonal entry and
the determinant of `t`. The half-power difference between the two
determinant shifts changes the lower normalized exponents to the
trailing exponents of the larger principal series.

This is the compact-support smooth section and covariance of
Jacquet's Godement construction in (7.1), with the inducing
positions reversed for the Library's upper Borel. The generation
of principal-series vectors by these sections and the identities
of their Whittaker coefficients are further steps in §7.
[Jacquet, *Archimedean Rankin–Selberg Integrals*, §7.1, pp. 43–46](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
