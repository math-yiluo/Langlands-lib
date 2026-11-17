# Actual component-quotient averaging

This unit combines actual identity-component equivariance with ordinary
finite-quotient averaging. `componentMatrixAverage` is the normalized sum
`σ(g) C ρ(g⁻¹)` over chosen representatives of the rational-point component
quotient. It is defined with an explicit finite quotient and invertible quotient
order. The matrix sum agrees on every vector with the abstract intertwiner
average implemented by Worker 544.

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
Worker 544's projection-preservation theorem shows it still maps into the
subspace and fixes it. Thus it yields an actual ambient equivariant projection.

The implementation is derived internal infrastructure for Milne, *Algebraic
Groups* (2022 corrected reprint), Exercise 4-3, printed p.97 / PDF p.108,
registered as `milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`.
The original exercise and full official errata snapshot were read. The paired abstract finite-quotient averaging and projection modules by
Worker 544 are retained unchanged as supporting files. This unit does not prove
the connected multiplicative-type classification or the full Nagata theorem.
