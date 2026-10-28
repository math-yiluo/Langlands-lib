# Compact conjugation averaging of actual smooth kernels

Author: Worker 813. Module:
`Langlands.Global.ArchimedeanKernelConjugationAverageProof`.

The theorem
`Langlands.Global.ArchimedeanGL.compactKernelConjugationAverage` proves the
published `Langlands.Global.ArchimedeanGL.CompactKernelConjugationAverageStatement K n`
for every `K : Type u` with `[Field K] [NumberField K]` and every `n : ℕ`,
including zero. The target is imported from
[`ArchimedeanKernelConjugationAverageStatement`](ArchimedeanKernelConjugationAverageStatement.md).
Its definitions and conventions are unchanged. The ambient measure `μ` is only
assumed to be a left Haar measure, as in the statement. The proof uses no right
invariance, inversion invariance or unimodularity of `μ`. It also fixes no Haar
normalization.

Helper declarations live in the namespace
`Langlands.Global.ArchimedeanGL.KernelConjugationAverage`.

## The averaged kernel

For the given probability Haar measure `ν` on `C = standardInfiniteCompact K n`,
`average ν κ x` is the Bochner integral

```lean
∫ k : standardInfiniteCompact K n, κ.val.val (k.val⁻¹ * x * k.val) ∂ν
```

The witness `η` is `average ν κ` with two proofs attached: it lies in
`smoothFunctions K n`, and it has compact support. So the first clause, the
pointwise formula, holds by `rfl`.

## Support and compactness

`saturation κ` is the set `{x | ∃ k, ∃ y ∈ tsupport κ, x = k * y * k⁻¹}` from the
statement. It is the image of the compact set `univ ×ˢ tsupport κ` in
`C × InfiniteAdelicGL K n` under the continuous map `(k, y) ↦ k * y * k⁻¹`. Compactness
of `C` is the published `isCompact_standardInfiniteCompact`. Compactness of
`tsupport κ` is the published `smoothCompactKernel_hasCompactSupport`. Hence
`isCompact_saturation` holds.

Take `x` outside the saturation. Then for every `k`, the point `k⁻¹ * x * k` lies
outside `tsupport κ`, since otherwise `x = k * (k⁻¹ * x * k) * k⁻¹` would lie in the
saturation. So the integrand vanishes identically and `average ν κ x = 0`. The
saturation is compact, hence closed, so it contains the closure of the support
(`tsupport_average_subset`). This is the second clause. A closed subset of a compact
set is compact, which gives `average_hasCompactSupport`.

## Genuine smoothness

Smoothness is real smoothness in the mixed coordinates `ArchimedeanMatrix K n`, with
the operator norm from `Matrix.Norms.Operator`. Let `c(k)` be the coordinate matrix
`archimedeanGLCoordinates K n k`. Then `conjugationMap k` is the continuous real-linear
map `a ↦ c(k)⁻¹ * a * c(k)`, built with `ContinuousLinearMap.mulLeftRight`. It depends
continuously on `k` (`continuous_conjugationMap`). On an invertible matrix `g` it
equals the coordinate matrix of the group conjugate (`conjugationMap_units`).

The published `Langlands.Analysis.compactLinearParameterIntegral` performs the
differentiation under the compact parameter integral. It is applied with these
inputs:

- parameter space `C`, parameter set `univ`, and the finite measure `ν`;
- `V = W = ArchimedeanMatrix K n`, with `s = t` the open range of `Units.val`;
- weight `f ≡ 1` and linear family `A = conjugationMap`;
- the function `φ = coordinateExtension K n κ.val`. It is smooth on that open set by
  the published `coordinateExtension_contDiffOn` from
  `Langlands.Global.ArchimedeanSmoothDifferential`.

The map `A` sends `s` into `t`, because conjugating an invertible matrix gives an
invertible matrix. The result is `ContDiffOn ℝ ∞` of
`a ↦ ∫ k in univ, 1 * φ (c(k)⁻¹ * a * c(k)) ∂ν` on the units. At each `g`, this gives
`ContDiffAt` at `(g : ArchimedeanMatrix K n)`. Composing with Mathlib's
`Units.contMDiff_val` gives a smooth map on the units manifold. On units, the
integrand is `κ (k⁻¹ * (coordinates⁻¹ g) * k)`, by `coordinateExtension_apply` and the
multiplicativity of the coordinate equivalence. So the composite is exactly the
coordinate expression of `average ν κ`, which is the `smoothFunctions` membership
(`average_mem_smoothFunctions`).

## Conjugation invariance, identity value, nonnegativity

- **Invariance.** For `k₀ ∈ C`, `average ν κ (k₀⁻¹ * x * k₀)` is rewritten using left
  invariance of `ν`, through `integral_mul_left_eq_self` with translation by `k₀`.
  Then `(k₀ * k)⁻¹ * x * (k₀ * k) = k⁻¹ * (k₀⁻¹ * x * k₀) * k`, proved by `group`.
- **Identity.** `k⁻¹ * 1 * k = 1`, so the integrand is constant and equal to `κ 1`.
  Its integral against the probability measure `ν` is `κ 1`.
- **Nonnegativity.** If every value of `κ` is real and nonnegative, then
  `κ z = ((κ z).re : ℂ)`. By `integral_complex_ofReal`, the average is the complex
  coercion of the real integral of `k ↦ (κ (k⁻¹ * x * k)).re`. That real integral is
  nonnegative by `integral_nonneg`, and its imaginary part is zero.

## Unchanged inverse-kernel integral

This clause is the only place where the ambient measure enters. The proof uses only
left invariance of `μ`.

**Right translation by a compact element** (`map_mul_right_apply_of_mem_compact`).
Let `H` be a locally compact Hausdorff topological group, `μ` a left Haar measure,
`L` a compact subgroup and `k ∈ L`. Mathlib's instance `isMulLeftInvariant_map_mul_right`
makes `map (· * k) μ` left invariant. So
`Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure` gives
`map (· * k) μ s = haarScalarFactor (map (· * k) μ) μ • μ s` on every set `s` with
compact closure. To show that the scalar is `1`, choose a compact neighbourhood `V`
of `1` and evaluate on `V * L`. This set is compact, it has positive finite
`μ`-measure because it contains `V`, and it is right `L`-invariant, so its preimage
under `· * k` is itself. Therefore `μ (V * L) = c • μ (V * L)`, and
`ENNReal.mul_eq_right` gives `c = 1`.

**Conjugation preserves compactly supported integrals**
(`integral_conj_of_mem_compact`). Let `φ` be compactly supported. Left invariance
gives `∫ φ (k⁻¹ * x * k) dμ = ∫ φ (x * k) dμ`. Through `integral_map_equiv` with
`MeasurableEquiv.mulRight k`, this equals `∫ φ d(map (· * k) μ)`. Both measures agree
on every measurable subset of the compact set `tsupport φ`, by the previous lemma,
so their restrictions to `tsupport φ` are equal. Since `φ` vanishes outside
`tsupport φ`, the lemma `setIntegral_eq_integral_of_forall_compl_eq_zero` reduces both
integrals to these equal restrictions.

**Fubini.** The function `(x, k) ↦ κ (k⁻¹ * x⁻¹ * k)` on
`InfiniteAdelicGL K n × C` is continuous, because the actual kernel is continuous
(published `continuous`). It vanishes outside the compact set
`(saturation κ)⁻¹ ×ˢ univ`. So `integral_integral_swap_of_hasCompactSupport` exchanges
the two integrals with no σ-finiteness hypothesis. Thus

```text
∫ average ν κ x⁻¹ dμ(x) = ∫_C ∫ κ (k⁻¹ * x⁻¹ * k) dμ(x) dν(k).
```

For each `k`, the inner integral is `∫ φ (k⁻¹ * x * k) dμ` with
`φ y = κ y⁻¹`, since `k⁻¹ * x⁻¹ * k = (k⁻¹ * x * k)⁻¹`. The function `φ` is compactly
supported, because inversion is a homeomorphism. The previous lemma, applied with
`L = C`, rewrites the inner integral as `∫ κ x⁻¹ dμ`. The outer integral of this
constant against the probability measure `ν` is the constant itself.

## Provenance and scope

This is an internal derived proof of the existing target. It combines published
Library results with Mathlib's Haar-measure uniqueness, product-integral and
manifold API. It does not claim to reproduce a theorem or proof from the
literature. Only this averaging target is proved. Normalized-kernel existence,
neighbourhood shrinkage, convolution approximation, compact-type projection and
reproduction are not addressed.
