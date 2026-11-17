# Schwartz bounds for compact right translates of a simple-root gauge

This internal development transports compact Iwasawa diagonal parameters to
the actual adelic group-scheme points used in Rankin–Selberg integrals.
`exists_compact_gaugeDiagonal_parameters` writes every point in a compact
set as u · gaugeDiagonalPoint(e) · k, with e in one compact set of idele
tuples, u adelic upper unipotent, and k in the standard compact subgroup.

Diagonal conjugation preserves the unipotent subgroup. Consequently
`gauge_diagonal_mul_iwasawa` reduces the value of a left unipotent and right
standard compact invariant gauge at diagonalPoint(d) · u · diagonalPoint(e)
· k to its value at diagonalPoint(d · e).

`gaugeRootTranslateMatrix` is the diagonal adelic matrix of the adjacent
ratios of e. It varies continuously with e.
`gaugeSimpleRootRow_mul` identifies the simple-root row of d · e with the
simple-root row of d multiplied by this matrix.

The product of the full idele norms of these ratios is strictly positive,
continuous, and multiplicative in the diagonal tuple. Its real power
with exponent −τ is therefore continuous and bounded above on the compact
set of parameters e. Taking the maximum of an upper bound and zero gives
a nonnegative real constant A.

Assume the published predicate `IsAdelicSimpleRootGauge F r τ Ξ`, and let
C be any compact subset of the actual adelic points. The theorem
`exists_compact_gaugeDiagonal_translate_majorant` constructs a
Schwartz–Bruhat function φ on rows of length r and A ≥ 0 such that, for
every diagonal idele tuple d and every c in C,

Ξ(gaugeDiagonalPoint(d) · c) ≤
ofReal(A) · ofReal(gaugeSimpleRootNormProduct(d)^(−τ)) ·
‖φ(gaugeSimpleRootRow(d))‖ₑ.

Indeed, compact Iwasawa parameters and the invariances reduce the left
side to Ξ(gaugeDiagonalPoint(d · e)). The defining torus formula for Ξ
then separates its norm-product weight by multiplicativity and the
real-power product identity. The matrices `gaugeRootTranslateMatrix(e)`
form a compact set. Applying `exists_compact_row_majorant` to that set
bounds the remaining translated Schwartz values by one φ. The previously
chosen A bounds the parameter-dependent weight. The construction retains
the original exponent τ and works for every natural r, including zero.

`exists_compact_gaugeSchwartz_kernel_majorant` also includes a
Schwartz–Bruhat function Φ on the full last-row space and any fixed real
exponent σ. It constructs φ on the simple-root row, ψ on a one-dimensional
row, and a nonnegative real A, all uniform over d and c in C. The full
kernel at gaugeDiagonalPoint(d) · c is bounded by

ofReal(A) · ofReal(gaugeSimpleRootNormProduct(d)^(−τ)) ·
‖φ(gaugeSimpleRootRow(d))‖ₑ · ‖ψ(singleRow(d_last))‖ₑ ·
ofReal(detNorm(gaugeDiagonalPoint(d))^σ).

For this extension the compact last-row theorem supplies ψ. Multiplicativity
of the determinant norm separates the right-translate factor
detNorm(c)^σ. Positivity and continuity of detNorm make this factor
continuous on C, hence bounded. Multiplying the previous A by the maximum
of this bound and zero gives the new constant. No lower bound on σ is
needed for this pointwise estimate; convergence requires a separate Mellin
argument.

This internal analytic estimate derives from the existing Iwasawa
theorem, the units topology, triangular matrix algebra and the uniform
Schwartz majorant construction. It assumes a supplied simple-root gauge;
it does not assert quotient integrability or prove the unconditional
Whittaker–Schwartz estimate.
