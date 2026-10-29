# Integration over a factorization `G = ι(X) K`

Author: Worker 235.

This module proves one theorem, `Langlands.CompactFactorization.lintegral_restrict_lintegral_mul`.
It is a helper for `Langlands.Representation.RankinSelberg.RecursiveQuotientIntegrationProof`, which
applies it to the Iwasawa factorization of `GL_(n+2)` into the standard parabolic subgroup of type
`(n+1, 1)` and the integral subgroup. The module defines nothing.

## Provenance

The content is derived and internal. It is the measure-theoretic core of the standard formula for
Haar measure on a group that factors as `G = P K` with `P` closed and `K` a subgroup. In the
literature this formula is usually stated for a left Haar measure on `P` and a Haar measure on a
compact `K`. Here the decomposition `G = P K` is abstracted to a parameter space `X` with a map `ι`,
and the left Haar property of the measure on `P` to the existence of measure-preserving maps that
represent left translations. No compactness, quotient measure or uniqueness theorem is used.

## Statement

Let `G` be a group with a measurable structure such that multiplication is jointly measurable
(`MeasurableMul₂ G`) and inversion is measurable (`MeasurableInv G`), and let `X` be a measurable
space. The hypotheses are:

- `μ : Measure G`, s-finite and left invariant;
- `K : Subgroup G` with measurable carrier `hK`;
- `ρ : Measure X`, s-finite, and a measurable map `ι : X → G`;
- `hfac`: every `y : G` is `ι x₀ * k₀` for some `x₀ : X` and `k₀ ∈ K`;
- `hσ`: for every `x₀ : X` there is a `ρ`-preserving map `σ : X → X` with
  `ι (σ x) = (ι x₀)⁻¹ * ι x` for every `x`;
- a measurable `F : G → ℝ≥0∞`.

The conclusion is

```text
∫⁻ k in K, ∫⁻ x, F (ι x * k) ∂ρ ∂μ = ρ (ι ⁻¹' K) * ∫⁻ y, F y ∂μ.
```

## Proof

All integrals are lower Lebesgue integrals, so Tonelli's theorem applies without integrability.

1. `h1`: swap the two integrals with `lintegral_lintegral_swap`. The integrand
   `(k, x) ↦ F (ι x * k)` is measurable because `ι` is measurable and multiplication is jointly
   measurable.
2. `h2`: for fixed `x`, write the `K`-integral as the full integral of the indicator of `K`
   (`lintegral_indicator`), and substitute `k = (ι x)⁻¹ * y` using left invariance
   (`lintegral_mul_left_eq_self`). The result is the integral over `y` of the indicator of
   `S = {(x, y) | (ι x)⁻¹ * y ∈ K}` times `F y`. The set `S` is measurable.
3. `h3`: swap the integrals again.
4. `h4`: for fixed `y`, the inner integral is `ρ (ι ⁻¹' K) * F y`. Write `y = ι x₀ * k₀` by `hfac`
   and take `σ` from `hσ`. Since `k₀ ∈ K`, the condition `(ι x)⁻¹ * ι x₀ * k₀ ∈ K` is equivalent to
   `(ι x₀)⁻¹ * ι x ∈ K`, that is to `ι (σ x) ∈ K` (`Subgroup.mul_mem_cancel_right`, `inv_mem_iff`).
   So the set of such `x` is `σ ⁻¹' (ι ⁻¹' K)`. Its measure is `ρ (ι ⁻¹' K)` because `σ` preserves
   `ρ` (`MeasurePreserving.measure_preimage`). The indicator integral is computed by
   `lintegral_mul_const` and `lintegral_indicator_one`.
5. The outer integral of `ρ (ι ⁻¹' K) * F y` is `ρ (ι ⁻¹' K) * ∫⁻ y, F y ∂μ`
   (`lintegral_const_mul`).

## Scope

The theorem does not identify `ρ` with a Haar measure, and it does not require `K` to be compact or
open; it only requires measurability of `K`. Right invariance of `μ` is not used.
