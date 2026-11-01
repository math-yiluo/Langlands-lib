# The two large integrands on the first-block fibers

Author: Worker 1037.

This module evaluates the published integrands of JPSS (1983), Sections 4.6–4.9 on
the fibers used in the first-block calculation. It is derived internal material.

## Character factor

`whittaker_blockRotation_firstBlockEmbedding_lowerRadical` proves
`W(C diag(v, 1) R(0; x) g) = ψ((x v⁻¹)_0) W(C diag(v, 1) g)` for every function in
the standard Whittaker space. Here `C` is the published block rotation. The proof
first moves the lower radical, `diag(v, 1) R(Z) = R(Z v⁻¹) diag(v, 1)`. It then
applies the published covariance of `W(C ·)` under the lower block unipotent group;
the diagonal blocks of a lower radical are trivial, and its corner entry is
`(x v⁻¹)_0`.

## Upper integrand

`upperIntegrand_fiberPoint_rowSnoc` uses the original total rank
`m 0 + (m 1 + 0 + 1) + 1`. The published upper integrand
`TwoBlockUnfolding.integrand`, at the fiber point `[diag(v, 1) R(y; x) g]`, equals
the product of:

- the published small integrand `unequalRankIntegrand ψ abv (m 1) 0 W' F 0 y [v]`
  at `s = 0`;
- `Φ((x, η) g)`.

Here `W'` is the right translate of the test function by `R(0; x) g`, and `F` is
the first-block coefficient function of `f(g)`. The half modulus gives exactly the
weight `|det v|^(-(m_1+1)/2)` of the small integrand.

## Lower integrand

`lowerIntegrand_firstBlockFiberPoint` holds for every total rank. The published lower
integrand at `[diag(v, 1) g]` is the product of three factors:

- the block-rotated test value `W(C diag(v, 1) g)`;
- the inverse half modulus times the first-block coefficient;
- the partial Fourier value of the preceding module.

## Transformed small integrand

`dualIntegrand_reflectionQuotient` uses the transformed total rank
`m 0 + (0 + m 1 + 1) + 1`. It evaluates, at the reflected point `[w v^ι]`, the
published small integrand of the transformed pair. That pair is the translate by
`blockWeylAt` of the first dual function, together with the second dual function.
The value is `W(C diag(v, 1)) W'(v) |det v|^(-(s - b/2))`.
