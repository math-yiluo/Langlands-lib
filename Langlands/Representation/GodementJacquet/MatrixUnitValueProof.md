# The unit is an actual matrix rational value

`Langlands.GodementJacquet.matrixUnitValue.{uF,uV}` proves the unchanged closed
proposition `MatrixUnitValueStatement`. It applies to every nonzero smooth
complex representation of `GL_(n+1)` over every canonical p-adic field, including
`n=0`, with independently universed field and representation carrier. This is an
internal compact-open construction. It requires no admissibility, character,
Fourier measure or functional-equation hypothesis.

First, `Padic.exists_biSmoothCoefficient_ne_zero` uses the published compact-open
cofinality theorem and smooth bidual injection. If every smooth functional
vanished on a nonzero vector, the smooth bidual injection would force that vector
to be zero. Thus there are a smooth functional `ℓ` and smooth vector `v` with
`ℓ(v) ≠ 0`. No finite-dimensionality of the carrier is used.

Next, `Padic.exists_matrixIntegral_one` chooses a compact open subgroup `K`
fixing `v`. The normalized determinant absolute value is one on `K`, by the
published compact-subgroup determinant theorem. The open embedding of the
general linear group into the full square matrix space makes its image `U`
compact and open. The characteristic function of `U` is therefore an actual
full-matrix Schwartz–Bruhat test, with support away from singular matrices.

Take the coefficient `f(g) = ℓ(v)⁻¹ ℓ(σ(g)v)`, which is an actual element of the
bi-smooth coefficient submodule and equals one on `K`. For the canonical group
Haar measure `μ`, take the test `Φ = μ(K)⁻¹ 1_U`, using its real mass embedded
in `ℂ`. The mass is positive because `K` is a nonempty open set, and finite
because `K` is compact. For every complex exponent `s`, the matrix integrand is
exactly `μ(K)⁻¹ 1_K`: the coefficient and determinant weight equal one on `K`,
and the test vanishes elsewhere. The indicator integrability theorem and
constant-indicator integral give absolute convergence and integral one for
every `s`.

`Padic.one_mem_matrixRationalValues` applies the construction at `s+n/2`.
The constant rational function one has denominator one and evaluates to one at
every `q^(-s)`, so it is an actual shifted rational value with bound zero for
both convergence and continuation. This proves membership before taking a
Laurent span.

Finally, `Padic.one_mem_iotaMatrixRationalValues` applies the ordinary construction
to the representation pulled back by the continuous inverse-transpose group
automorphism. Continuous pullback preserves smoothness, and
`iotaMatrixRationalValues_eq_comp_inverseTranspose` identifies its ordinary
rational values with the original transformed family. Thus the original
inverse-transpose coefficient family also attains one. The last theorem
packages the two memberships into the exact closed target.

The result supplies a unit value for normalized-generator arguments. It does
not assert a common denominator, rationality for arbitrary tests, or a
functional equation.
