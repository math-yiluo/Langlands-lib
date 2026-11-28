# The value of the spherical section on the open cell

Module `Langlands.Representation.Shahidi.OpenCellValue`, namespace
`Langlands.Shahidi.OpenCell`.

## Contents

- `IsOpenCellSection K ψ hϖ a c s f`: the transformation law of the function `f` in
  `Langlands.Shahidi.UnramifiedOpenCellSumStatement`,
  `f(u(X) diag(m₁, m₂) k) = δ_P(m₁, m₂)^(1/2 + s/N) W°(m₁; a) W°(m₂; c)` for integral `k`,
  `N = r + t + 2`.
- `blockWeyl_mem_integralSubgroup`: the block Weyl element is integral.
- `normalizedAbs_zpow_of_isUniformizingElement`, `determinantNorm_unipotent_mul_torus`:
  `|ϖ^k| = q^(-k)` and `|det(u ϖ^λ)| = q^(-∑ λ_i)` for upper unipotent `u`.
- `exists_openCellSection_value`: for every `Y` there are upper unipotent `u₁`, `u₂` with
  `f(lower(Y) k') = (q^(-N D))^(1/2 + s/N) W°(u₁ ϖ^λ; a) W°(u₂ ϖ^μ; c)` for all integral `k'`,
  where `λ`, `μ` are the two blocks of `openCellExponent hϖ Y` and `D = openCellDepth hϖ Y`.

## Provenance

Derived from the transformation law and the Iwasawa decomposition of `lower(Y)`
(`Langlands.Representation.Shahidi.OpenCellGeometry`).
