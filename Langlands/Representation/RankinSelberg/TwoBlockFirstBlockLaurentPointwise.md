# The first-block Laurent identity at a representative

Author: Worker 1037.

This module proves `pointwise_laurent_identity`, the identity of JPSS (1983),
Section 4.9 at a single representative `g` of the lower mixed quotient. It is
derived internal material. The hypotheses are:

- full Whittaker type of `π`;
- inverse-character Whittaker type of the first block;
- nonzero functionals;
- the two normalized-generator certificates and the rational-continuation and
  normalized-functional-equation data of the original block `j = m 1`, `k = 0`;
- the abstract kernel `Kf` of the lower coefficient lemma;
- measurability and finiteness of the iterated upper fiber integrals at `g`.

Write `SL(k)` and `SU(k)` for the two coefficient series below. The conclusion is

`Pdual(q⁻¹X⁻¹) • SL = (C(ζ^t c_ε) T^d P) • SU`,

where:

- `SL(k) = q^(-k b) ∫_{AQ_k} Elow([diag(v, 1) g])`;
- `SU(k) = ∫_Z ∫_{AQ_k} Eup([diag(v, 1) R(Z) g])`.

For each row `x`, the published `smallFE_coefficient_identity` gives
`Pdual(q⁻¹X⁻¹) • reflectSeries q a'_x = (C(ζ^t c_ε) T^d P) • a_x`. Its inputs are:

- the series interfaces `smallIntegral_series` and `dualSmallIntegral_series`;
- membership of the rational continuations in the actual value sets.

Here `a_x` and `a'_x` are the original and transformed slice coefficients of the
model vectors defined in the Coefficients module: the translate of the test vector
by `R(0; x) g`, and the first-block coefficient function. By the two coefficient
lemmas, `SU` and `SL` are the coefficientwise row integrals of `Φ((x, η) g) a_x`
and of `Φ((x, η) g) reflectSeries q a'_x`.

The finite Laurent action commutes with the scalar `Φ((x, η) g)`. The published
`integral_laurent_identity_ae` therefore integrates the per-row identity
coefficient by coefficient. No polynomial factor is cancelled.
