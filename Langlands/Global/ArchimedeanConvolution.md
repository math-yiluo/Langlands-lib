# Compact smooth archimedean kernels and raw right convolution

This is internal analytic infrastructure for the automorphic differential-growth
route. It works for every `K : Type u` with `[Field K] [NumberField K]` and every
`n : ℕ`. All declarations are in `Langlands.Global.ArchimedeanGL`. It imports
`InfiniteAdelicGL` from `Langlands.Global.AdelicGL` and the actual mixed-coordinate
smooth functions and enveloping differential action through
`Langlands.Global.ArchimedeanEnvelopingAction`. No existing group, topology,
smoothness predicate or differential action is replaced.

## Kernel space

`compactlySupportedSmoothFunctions K n` is the complex submodule of
`SmoothFunctions K n` whose underlying complex functions have `HasCompactSupport`,
i.e. compact closure of their nonzero support. `SmoothCompactKernel K n` is its
carrier. If `κ` is a kernel, `κ.val` is the published smooth function and
`κ.val.val` is its underlying function on the completion-based group.
`kernelToContinuousMap` is the complex-linear inclusion obtained from the
published `toContinuousMap`; its pointwise formula and compact-support property
are exposed by `kernelToContinuousMap_apply` and
`smoothCompactKernel_hasCompactSupport`.

The submodule laws use compact-support preservation under sums and scalar
multiplication. Smoothness is the existing real manifold smoothness in mixed
real/complex matrix coordinates. No new regularity field is assumed.

## Original topology and Haar measure

`infiniteAdelicGL_t2Space` and `infiniteAdelicGL_locallyCompactSpace` are instances
for the original topology on `InfiniteAdelicGL K n`. Hausdorffness comes from the
product of the actual archimedean completions. For local compactness, the infinite
adele ring is a finite product of locally compact completions, finite matrices
have the product topology, and Mathlib's units construction is locally compact.
Thus these are properties of the already published topology, not a transported
replacement topology. They are compatible with the published coordinate
homeomorphism in `ArchimedeanGL`.

`borelMeasurableSpace K n` is exactly the Borel sigma algebra of that topology,
and `borelMeasurableSpace_borelSpace` proves this equality. The measurable
structure is a definition available for local installation, not a global
measurable-space instance. The measure-generic API accepts any
`[MeasurableSpace (InfiniteAdelicGL K n)]` with the corresponding `BorelSpace`.

For each such structure, `leftHaarMeasure K n` is Mathlib's constructed
`Measure.haar`, using the local compactness proved here.
`leftHaarMeasure_isHaarMeasure`, `leftHaarMeasure_ne_zero`, and
`exists_leftHaarMeasure` establish its Haar properties and nonzeroness.
`IsHaarMeasure` supplies left invariance, finiteness on compact sets and positivity
on nonempty open sets. The choice follows Mathlib's normalization on an
arbitrarily chosen positive compact set; no coordinate-volume normalization is
claimed. `exists_borelLeftHaarMeasure` installs the explicitly defined Borel
structure locally and proves nonzero Haar existence with no measurable-space or
measure-existence hypothesis.

## Integral convention and linearity

`rawConvolution K n μ f κ g` is definitionally

```text
∫ y, f(y) * κ(y⁻¹ * g) dμ(y).
```

Here `f : C(InfiniteAdelicGL K n, ℂ)` is an arbitrary continuous function and
`κ : SmoothCompactKernel K n`. Specializing `μ` to `leftHaarMeasure K n` gives
the required left-Haar right convolution. The definition itself accepts any
measure. This permits later estimates with a supplied left-invariant measure.

Under `BorelSpace` and `IsFiniteMeasureOnCompacts μ`,
`convolution_integrable` proves pointwise Bochner integrability. For fixed `g`,
the map `y ↦ y⁻¹ * g` is a homeomorphism. Pulling back the kernel by it preserves
compact support. Multiplying by `f` preserves that support bound, and the
integrand is continuous. Mathlib's continuous compact-support integrability
theorem then applies. This proof needs no invariance of `μ`.

`rawConvolution_add_left`, `rawConvolution_add_right`,
`rawConvolution_smul_left`, and `rawConvolution_smul_right` prove complex
linearity in both inputs using integral additivity and scalar multiplication.
The scalar identities do not require compact finiteness or Borel compatibility.
`rawConvolutionLinear` bundles the bilinear operation with codomain
`InfiniteAdelicGL K n → ℂ`. `rawConvolution_apply` and
`rawConvolutionLinear_apply` give the exact integral formula. No continuity or
smoothness of the output, transfer of enveloping differentiation, or reproducing
kernel is asserted or assumed in this unit.

## Rank zero and provenance

At `n = 0`, the empty matrix group has a single element.
`hasCompactSupport_rankZero` proves that every member of `SmoothFunctions K 0`
has compact support. The topology, nonzero Haar existence, integrability and
bilinearity constructions all apply without a positive-rank hypothesis.

The mathematical construction is internal, derived from the published group and
smooth-function definitions and the cited Mathlib constructions. Its motivation
is Borel–Jacquet, *Automorphic forms and automorphic representations* (1979),
§2.2, printed p.193 / PDF p.188 of Corvallis Part I, registered as
`borel-jacquet-1979-automorphic`, SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
That passage motivates compact smooth reproducing convolution and subsequent
derivative bounds; those additional assertions are outside this construction.
The original page was read and no corresponding project erratum was found.
