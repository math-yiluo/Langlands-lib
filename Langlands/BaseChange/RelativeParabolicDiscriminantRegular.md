# Nonvanishing of the relative parabolic discriminants

`RelativeParabolicDiscriminantRegularStatement` asserts that if the image of a
standard Levi element `m` is regular semisimple in `GL_n(K)`, then
`relativeParabolicDiscriminant B K m` is nonzero. The theorem
`relativeParabolicDiscriminant_ne_zero` proves this over an arbitrary field `K`.

`twistedRelativeParabolicDiscriminant_ne_zero_of_cyclicNorm` gives the twisted
consequence for a cyclic field extension: if the norm of the embedded `δ`
equals the scalar extension of the embedded regular semisimple `γ`, with both
points in their respective standard Levis, then the twisted relative factor is
nonzero in the base field. It uses
`twistedRelativeParabolicDiscriminant_eq_of_cyclicNorm` and introduces no extra
characteristic or ramification hypothesis.

This is a derived algebraic verification of nonvanishing for the inverse
relative factors used in Henniart–Lemaire (2011), II.4.5, formulas (1) and (3),
printed pp. 86 and 88 (PDF pp. 94 and 96).

## Implemented proof

Suppose a matrix class `[X]` is killed by `1 − Ad(m)⁻¹`. The matrix
`Ad(m)⁻¹(X) − X` then belongs to the block diagonal submodule. For distinct
blocks `i,j`, let `P_i` and `P_j` be their coordinate projections, viewed as
diagonal matrices. They commute with the embedded `m` and its inverse.
Sandwiching the difference by those projections shows that `Y = P_i X P_j`
commutes with the embedded `m`. Also `Y² = 0` because `P_j P_i = 0`.

Thus `1 + Y` is a general linear element with inverse `1 − Y`, and it commutes
with the embedded regular semisimple point. The regular centralizer containment
`mem_leviSubgroup_of_commute_regular` implies that `1 + Y` is in the standard
Levi, so the `(i,j)` block of `X` vanishes. Applying this to each off-block
position makes `[X]` zero. The determinant criterion for a finite-dimensional
linear endomorphism now gives ordinary nonvanishing, and the exact-norm relative
comparison gives twisted nonvanishing.

The proof does not assert a Haar Jacobian, a character identity, or an orbital
integral formula.
