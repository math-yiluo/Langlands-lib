# The two large first-block coefficients as row integrals of small coefficients

Author: Worker 1037.

This module carries out, at a fixed representative `g`, the row split and the
small-integral identification of JPSS (1983), Section 4.9, printed pages 416–418.
It is derived internal material. The supplied self-dual measure `ν`, its row measure
and its rectangular product measures are used unchanged.

## Upper coefficient

`upper_coefficient_eq_rowIntegral` assumes the original rank equality
`t = m 0 + (m 1 + 0 + 1)`. Its hypotheses are joint measurability and finiteness of
the iterated absolute integral of `(Z, q) ↦ Eup([diag(v_q, 1) R(Z) g])` on the
`b × a` rectangle times the slice `k`. Under them the iterated upper fiber integral
`∫_Z ∫_{AQ_k} Eup` equals `∫_x Φ((x, η) g) a_x(k) dx`. Here `a_x` is the original
small slice coefficient series of the pair formed by:

- the translate of the test function by `R(0; x) g`;
- the first-block coefficient function of `f(g)`.

The row function is also shown to be integrable. The proof uses the published
row-split Fubini lemma `integral_rectangular_rowSnoc` and the upper fiber formula.

## Lower coefficient

`lower_coefficient_eq_rowIntegral` assumes the transformed rank equality
`t = m 0 + (0 + m 1 + 1)`. It proves

`q^(-k b) ∫_{AQ_k} Elow([diag(v, 1) g]) = ∫_x Φ((x, η) g) (reflectSeries q a'_x)(k) dx`,

where `a'_x` is the transformed small slice coefficient series of the same pair.
The hypotheses are an abstract kernel `Kf x [v] = ψ((x v⁻¹)_0)` with norm at most
one and joint measurability, and integrability on the slice of the reflected
transformed integrand.

The proof proceeds in four steps:

1. Reflect `[v] ↦ [w v^ι]`, which turns slice `-k` into slice `k`.
2. Evaluate the reflected transformed integrand as `Kf x · A`.
3. Rearrange with the published lemma `integral_mul_integral_swap`.
4. Apply `lower_slice_scalar`.

On slice `k`, `lower_slice_scalar` identifies the following scalar product: the
lower density `q^(-k b)` times the inverse half modulus times the Jacobian
`|det v|⁻¹`, with `q^k` times the transformed weight `|det v|^(b/2)`.

## Auxiliary lemmas

`integrable_rowRestriction` proves integrability of `x ↦ Φ((x, η) g)`.
`ae_lintegral_kernel_comp_lt_top` is a generic Tonelli consequence: under two
composite lintegral laws, the iterated absolute fiber integral of an integrable
function is almost everywhere finite.
