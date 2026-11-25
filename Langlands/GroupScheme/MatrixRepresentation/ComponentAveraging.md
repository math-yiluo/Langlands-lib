# Actual component-quotient averaging

This module combines actual identity-component equivariance with ordinary
finite-quotient averaging. `componentMatrixAverage` is the normalized sum
`σ(g) C ρ(g⁻¹)` over chosen representatives of the rational-point component
quotient. It is defined with an explicit finite quotient and invertible quotient
order. The matrix sum agrees on every vector with the abstract intertwiner
average `FiniteQuotientAveraging.intertwinerAverage`.

For an affine group locally of finite type over an algebraically closed field,
a supplied open identity-component subgroup with all-test normal range makes
this average an actual ambient intertwiner. Each summand retains actual
subgroup equivariance by normal conjugation; abstract finite-quotient averaging
makes the sum equivariant under rational ambient points. The component-translate
open cover then glues these identities to equivariance on every affine test,
without any reducedness assumption.

`exists_equivariantProjection_of_componentProjection` applies the matrix
average to an actual identity-component-equivariant projection onto an ambient
stable subspace. The averaged matrix is actually ambient equivariant, and
the projection-preservation theorem `intertwinerAverage_isProj` shows it still maps into the
subspace and fixes it. Thus it yields an actual ambient equivariant projection.

The implementation is derived internal infrastructure for Milne, *Algebraic
Groups* (2022 corrected reprint), Exercise 4-3, printed p.97 / PDF p.108,
registered as `milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`.
The original exercise and full official errata snapshot were read. The abstract finite-quotient averaging and projection modules
`Representation.FiniteQuotientAveraging` and `Representation.FiniteQuotientProjection`
are supporting files. This module does not prove
the connected multiplicative-type classification or the full Nagata theorem.
