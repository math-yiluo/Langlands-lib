# Smooth compact convolution and transfer of real generators

`Langlands.Global.ArchimedeanGL.compactKernelConvolutionRealDifferentiation`
proves the whole published proposition
`Langlands.Global.ArchimedeanGL.CompactKernelConvolutionRealDifferentiationStatement K n`.
Its parameters are `(K : Type u) [Field K] [NumberField K] (n : ℕ)`, with no
additional premise. It imports the unchanged statement from
`ArchimedeanConvolutionRealDifferentiationStatement`.

For every compatible Borel measurable structure on `InfiniteAdelicGL K n`,
measure `μ` finite on compact sets, continuous complex function `f`, and smooth
compact kernel `κ`, the theorem constructs a smooth function `F` whose value is
exactly

```text
g ↦ ∫ y, f y * κ.val.val (y⁻¹ * g) ∂μ.
```

The same `F` satisfies, for every real Lie algebra element `X` and every `g`,

```text
(smoothDifferential K n X F).val g
  = ∫ y, f y * (smoothDifferential K n X κ.val).val (y⁻¹ * g) ∂μ.
```

All natural ranks, including zero, are covered. The proof uses no invariance or
nonvanishing of the measure, positive dimension, smoothness or global
boundedness of `f`, or reproduction identity.

The helper declarations below are in the namespace
`Langlands.Global.ArchimedeanGL.CompactConvolution`.

## A uniform compact integration region

`exists_compact_support` takes a compact neighborhood `L` of `g` in the original
group topology and sets

```text
k = L * (tsupport κ.val.val)⁻¹.
```

The set `k` is compact by continuity of multiplication and inversion. If `x ∈ L`
and `y⁻¹ * x` belongs to the kernel's topological support, then
`y = x * (y⁻¹ * x)⁻¹ ∈ k`. Consequently, for every `x` in a neighborhood of
`g`, the kernel vanishes at `y⁻¹ * x` whenever `y ∉ k`. This gives a single
compact set for nearby output points, without changing the integration
variable or the measure.

`extension_eq_raw` uses this implication and
`setIntegral_eq_integral_of_forall_compl_eq_zero` to identify the compact
integral with the full raw convolution.

## The matrix-parameter integral

Write `M = ArchimedeanMatrix K n`, and let `c` be
`archimedeanGLCoordinates K n`. The helper `leftLinear y` is the continuous
real-linear map

```text
A(y) : M →L[ℝ] M,     A(y)(a) = c(y⁻¹) * a.
```

`continuous_leftLinear` proves continuity of this family, using continuous
inversion, the published coordinate equivalence, units valuation, and the
continuous bilinear multiplication on the normed real matrix algebra.
`leftLinear_mem_range` proves that these maps preserve the open range `U` of
units valuation.

Set `φ = coordinateExtension K n κ.val`. The published
`coordinateExtension_contDiffOn` gives real smoothness of `φ` on `U`.
For a fixed compact `k`, define

```text
H(a) = ∫ y in k, f y * φ(A(y)(a)) ∂μ.
```

This is the helper `extension`. The identity `extension_apply` identifies its
value at `c(g)` with the compact integral of `f y * κ.val.val (y⁻¹ * g)`.
`extension_contDiffOn` and `extension_hasFDerivAt` apply the published theorem
`Langlands.Analysis.compactLinearParameterIntegral` with parameter and target
spaces both equal to `M`, and with source and target open sets both equal to
`U`. They give real smoothness of `H` on `U` and its actual derivative there:

```text
DH(a) = ∫ y in k, f y • ((fderiv ℝ φ (A(y)(a))).comp (A(y))) ∂μ.
```

`derivative_integrable` separately supplies integrability of this
continuous-linear-map-valued integrand on `k`. It specializes the published
affine helper `CompactLinearParameterIntegral.continuousOn_partialDeriv` to
zero offset, restricts the continuous family to the slice at `a = c(g)`, and
uses compact integrability. This justifies the later use of
`ContinuousLinearMap.integral_apply`.

## Constructing the smooth lift and transferring the derivative

For each point in the units group, `raw_mem_smoothFunctions` chooses the local
compact integration set above. It composes the real smoothness of `H` with the
smooth units valuation and uses the local equality with the raw integral.
Thus the raw convolution belongs to the published submodule `smoothFunctions`.
The exported theorem takes this very function as the value of `F`.

`coordinateExtension_eventuallyEq` transports a local equality on the original
group to an equality on a matrix neighborhood of `c(g)`. It uses the coordinate
homeomorphism and `Units.isOpenEmbedding_val.map_nhds_eq`. Applied to the local
compact integral, it identifies the Fréchet derivative of
`coordinateExtension K n F` with that of `H` at `c(g)`.

The theorem evaluates the resulting continuous-linear-map integral in the
published direction `c(g) * realLieAlgebraToMatrix K n X`. For each `y`,
associativity gives

```text
A(y)(c(g) * X) = (c(y⁻¹) * c(g)) * X = c(y⁻¹ * g) * X.
```

Here `X` in a matrix expression denotes `realLieAlgebraToMatrix K n X`.
By `smoothDifferential_apply`, the evaluated derivative integrand is exactly
`f y * (smoothDifferential K n X κ.val).val (y⁻¹ * g)`.
There is no sign, antipode, or adjoint factor.

Finally, outside `k` the differentiated kernel also vanishes. The proof invokes
the published `smoothDifferential_eq_zero_of_notMem_tsupport` from
`ArchimedeanEnvelopingSupportProof`, rather than proving support preservation
again. The same compact/full integral equality then yields the stated identity
over the entire original group.

## Provenance and scope

This is an internal matrix-coordinate specialization and local-support argument
for the published real-generator target. The substantial analytic input is the
separately published `CompactLinearParameterIntegralProof`, which establishes
smoothness and differentiation by compact domination and induction through
directional derivatives. The present proof supplies the group support region,
the actual linear family in the existing chart, the smooth lift, and the
`gX` chain-rule identification. It uses the existing support theorem and changes
none of those imported definitions or statements.

The proof establishes the real-generator assertion only. The extension to the
complexified enveloping algebra, reproduction, and automorphic differential
growth are separate results.
