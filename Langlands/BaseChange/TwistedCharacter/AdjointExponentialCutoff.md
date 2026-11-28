# Invariant exponential cutoff of the descended slice distribution

Let `T` be the distribution on a semisimple descent domain and `T₀` an invariant distribution on the fixed algebra which agrees with `T` on tests supported in a clopen neighborhood of zero. `exponentialCutoffDistribution` restricts each test to the clopen exponential source, transports it by `exp − 1` with zero extension, and applies `T₀`.

`AdjointExponentialCutoffStatement` produces an invariant distribution in additive exponential coordinates from an invariant clopen exponential domain. Conjugation commutes with `exp − 1` and preserves its source, so the test transport commutes with conjugation. The resulting distribution agrees with `T` on each sufficiently small exponential congruence chart. The theorem also records the agreement with `T₀` under the same chart in the fixed algebra.

For a test on the congruence subgroup, the additive extension uses the inverse exponential chart. After applying `exp − 1`, its support and values are those of the extension through the coordinate `m − 1`. This coordinate lies in the clopen neighborhood on which `T₀` agrees with `T`. The comparison keeps the test values in their given normalization.

This is the restriction, pullback, and zero extension of the descended distribution used before the Fourier vanishing criterion. [Clozel, *Characters of non-connected, reductive p-adic groups*, §3.4, p. 155](https://doi.org/10.4153/CJM-1987-008-3)
