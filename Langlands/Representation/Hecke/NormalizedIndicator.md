# Normalized compact-open Hecke indicators

For an actual open subgroup K with compact underlying set and a genuine left Haar measure μ, this module defines `HeckeAlgebra.normalizedIndicator μ K hK` to be `(μ(K).toReal : ℂ)⁻¹` times the published compact-open subgroup indicator. The compact set has finite mass and its nonempty open interior has positive mass, so the real and complex normalizing constants are nonzero. The carrier and multiplication are those of the actual convolution algebra. No second-countability, sigma-finiteness, unimodularity, or normality assumption on K is imposed.

The two pointwise formulas are

- `(e_K * f)(x) = μ(K)⁻¹ ∫_{k∈K} f(k⁻¹*x) dμ(k)`;
- `(f * e_K)(x) = μ(K)⁻¹ ∫_{k∈K} f(x*k) dμ(k)`.

The first formula expands the indicator and rewrites its integral as a restricted integral. The second first substitutes `y = x*k` using left invariance of μ, then uses subgroup closure under inversion to identify the indicator of k⁻¹ with that of k. This explains both the absence of an inverse in the right average and the absence of a modular factor. Both integrands are continuous on a compact set; integrability also follows from the already proved integrability of the convolution integrands and the indicated left substitution.

The indicator is bi-K-invariant because scalar multiplication preserves the published invariant submodule. A left-K-invariant function is fixed by the left average, and a right-K-invariant function is fixed by the right average: on K the integrand is constant, whose integral is μ(K) times that value. The nonzero normalization cancels this factor. Applying this to the indicator proves idempotence intrinsically. For L contained in K, e_K is also bi-L-invariant, so `e_L*e_K = e_K = e_K*e_L`.

The normalization comparison reuses `Langlands.RankinSelberg.normalizedCompactOpenHaar` and its proved mass-one identity. With this Haar choice e_K is exactly the unnormalized indicator. The measure is not reconstructed or assumed to have mass one.

Source: Flath, *Decomposition of representations into tensor products* (1979), section 1, printed p.179 / Corvallis Part I PDF p.175, registered `flath-1979-tensor-products`, SHA256 `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`, defines e_K and the bi-invariant corner. The integral convention is that of Folland, *A Course in Abstract Harmonic Analysis*, second edition (2015), section 2.5, printed pp.54–56 / PDF pp.67–69, formula (2.36), registered `folland-2015-abstract-harmonic-analysis-second`, SHA256 `c82467bfa77428c32d3e1a5d1cbdc11129511e0c61da2f9d8fbc717776b9e542`. These averaging and refinement proofs are derived calculations implementing those definitions. This unit supplies the actual idempotents and local-unit identities; the unital corner structure is a subsequent unit.
