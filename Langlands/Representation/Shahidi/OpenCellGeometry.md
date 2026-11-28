# Geometry of the two-block open cell

Module `Langlands.Representation.Shahidi.OpenCellGeometry`, namespace
`Langlands.Shahidi.OpenCell`. Block computations for the open cell of the upper two-block
parabolic of `GL_(m+n)` and the Iwasawa data of the lower radical matrices.

## Contents

- `blockWeyl_mul_intertwiningUnipotent`: `w u'(Y) = lower(Y) w`, where `w = blockWeyl m n`,
  `u'(Y) = intertwiningUnipotent m n Y` and `lower(Y) = [[I_m, 0], [Y, I_n]]`
  (`Shahidi.lower`).
- `topLeft`, `botRight`: the diagonal blocks of an invertible upper triangular matrix, as
  elements of `GL_m` and `GL_n`; `radicalCoordinate` and `eq_upper_mul_blockSum`:
  `b = u(X) · diag(b₁₁, b₂₂)`. The blocks of `u ϖ^ν` (`topLeft_mul_torus`,
  `botRight_mul_torus`) are the blocks of `u` times the corresponding torus elements, and the
  blocks of an upper unipotent matrix are upper unipotent.
- `lower_inv`, `lower_add`, `det_lower`: `lower` is an additive-to-multiplicative
  homomorphism with determinant one.
- `openCellExponent hϖ Y`: the Iwasawa exponent (`Iwasawa.exponent`) of `lower(Y)`.
  `openCellExponent_castAdd_nonneg` and `openCellExponent_natAdd_nonpos`: on the first block it
  is componentwise nonnegative and on the second block componentwise nonpositive; this uses
  that the first diagonal block of the Iwasawa factor is the top-left block of
  `lower(Y) k⁻¹`, which is integral, and that the inverse of the second block is a block of
  `k lower(-Y)`.
- `openCellDepth hϖ Y = ∑_i λ_i ≥ 0` (sum of the first-block exponents); by
  `sum_openCellExponent` the second-block exponents sum to `-openCellDepth`.
- `uniformizer_pow_depth_mul_mem`: `ϖ^D Y` is integral for `D = openCellDepth Y`, via the
  adjugate formula for the inverse of the second Iwasawa block.

## Provenance

These are elementary matrix computations used for the open-cell sum of
`Langlands.Shahidi.UnramifiedOpenCellSumStatement`; the sign pattern of the Iwasawa weights is
the one described in the Markdown of that statement (comparison with the source, last item).
