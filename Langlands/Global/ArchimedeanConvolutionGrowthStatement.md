# Polynomial growth under a compactly supported convolution kernel

Documentation correction (P3-057): Worker 1057.

This unit states an elementary analytic prerequisite for the automorphic
differential-growth proof. It uses the published actual group
`Langlands.Global.InfiniteAdelicGL K n` and its matrix/inverse height. This
module proves only the logical implication between the two formulations below.
The convolution estimate itself is proved separately; see Status below. Neither
this module nor that proof constructs a reproducing kernel or asserts growth of
derivatives of arbitrary smooth functions.

## Statements and conventions

In namespace `Langlands.Global.ArchimedeanGL`,
`CompactKernelConvolutionBoundStatement K n` quantifies over every Borel-compatible
measurable-space instance on the actual infinite adelic matrix group and every
left-invariant measure `μ` finite on compact sets. For all continuous complex
functions `f` and `κ`, with `κ` compactly supported, every real `C ≥ 0` and natural
`d` such that `‖f(g)‖ ≤ C * matrixHeight K n g ^ d`, it asserts existence of a
real `D ≥ 0` satisfying

```text
‖∫ y, f(y) * κ(y⁻¹ * g) dμ(y)‖ ≤ D * matrixHeight K n g ^ d
```

for every `g`. The measure is not assumed nonzero: the statement also includes
the zero measure. A nonzero left Haar measure is constructed separately, by
`leftHaarMeasure`, `exists_leftHaarMeasure` and `exists_borelLeftHaarMeasure` in
`Langlands.Global.ArchimedeanConvolution`. No measurable-space instance or
normalization is added to the Library by this statement. The Bochner integral
is the ordinary Mathlib integral; no integrability or derivative estimate is
supplied as a hypothesis. The published proof justifies its integration steps
from the continuity and compact support of `κ` and the height bound on `f`.

The convention `f(y) κ(y⁻¹g)` is chosen so that a right-translation-generated
differential, whose real-generator direction is `gX`, acts on the second
factor. Transfer of that differential under the integral is not part of this
unit. It is proved separately, for smooth compactly supported kernels, by
`compactKernelConvolutionRealDifferentiation` and
`compactKernelConvolutionDifferentiation`; see Status below. This unit has no
dependency on the construction of a smooth kernel subtype or on differential
covariance.

`CompactKernelConvolutionGrowthStatement K n` has the same measure, continuity,
and compact-support quantifiers, but assumes and concludes the existing
`HasPolynomialGrowth` predicate. Its exponent and constant are existential.
The theorem `compactKernelConvolutionGrowth_of_bound` merely unpacks the input
growth witnesses, applies the proposed bound statement, and packages the
resulting constant together with the original exponent. It does not supply a
proof of either statement.

Both proposition definitions retain arbitrary number fields `K : Type u`,
arbitrary universe `u`, and every natural rank, including zero. The empty-matrix
group is handled by the same formula. No positive rank, discrete quotient,
arithmetic subgroup, compact-finiteness, or center-finiteness hypothesis is
needed for this elementary integral bound. Those last two hypotheses remain
essential in the separate reproducing-kernel step for actual automorphic forms.

## Provenance and intended use

The statements are internal analytic infrastructure motivated by Borel and
Jacquet, *Automorphic forms and automorphic representations* (1979), §2.2,
printed p.193 / one-based PDF188. That passage obtains growth of enveloping
derivatives from a compactly supported smooth reproducing convolution kernel.
The raw compact-kernel estimate here isolates its elementary integration step
for the Library's already defined height. Sections 4.2–4.3, printed pp.194–195 /
PDF189–190, give the adelic per-finite-slice setting. These pages and the
bibliography on PDF197 were read. No project errata entry for this source was
found. The cross-reference slips in §2.2 are documented in the published
`Langlands.Automorphic.PreservationStatement.md`; this unit relies on the
content of its growth sentence, not its printed condition labels.

The new statements are not quotations of a numbered source theorem. The
extension from smooth kernels to continuous compactly supported kernels,
measure-generic quantification, and explicit matrix-height formulation are
internal choices. The expected estimate uses left invariance with `y = g z`,
so the integral becomes `∫ z, f(g z) κ(z⁻¹) dμ(z)`, and then uses
`matrixHeight(g z) ≤ matrixHeight(g) * matrixHeight(z)`. The remaining weighted
kernel norm is integrable by compact support. This module does not implement
that route. The published proof `compactKernelConvolutionBound` follows it.

The parent target remains exactly
`Langlands.Automorphic.AutomorphicDifferentialGrowthStatement K n`, which is
unproved. Applying these statements to that target still requires proving
existence of a smooth reproducing kernel from the actual automorphic
hypotheses. That obligation is neither assumed nor discharged here or in the
published results below. Two other ingredients of that application are
published separately. Transfer of genuine enveloping differentiation to a
smooth compactly supported kernel is `compactKernelConvolutionDifferentiation`.
Preservation of compact support under enveloping derivatives is
`envelopingCompactSupport`.

Registered source: `borel-jacquet-1979-automorphic`.
Original: `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`.
SHA256: `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.

## Status

This module's proposition definitions are proved by published theorems in
other modules. None of these results proves the automorphic growth target.

- `Langlands.Global.ArchimedeanGL.compactKernelConvolutionBound` in
  `Langlands.Global.ArchimedeanConvolutionGrowthProof` proves
  `CompactKernelConvolutionBoundStatement K n` with all of its quantifiers.
  The corollary `compactKernelConvolutionGrowth` in the same module proves
  `CompactKernelConvolutionGrowthStatement K n` through
  `compactKernelConvolutionGrowth_of_bound`.
- `Langlands.Global.ArchimedeanGL.compactKernelConvolutionDifferentiation` in
  `Langlands.Global.ArchimedeanConvolutionDifferentiationProof` proves
  `CompactKernelConvolutionDifferentiationStatement K n`. For every
  Borel-compatible measurable structure, every measure `μ` finite on compact
  sets (left invariance is not required), every `f : C(InfiniteAdelicGL K n, ℂ)`
  and every smooth compactly supported kernel `κ : SmoothCompactKernel K n`, the
  raw convolution `rawConvolution K n μ f κ` is a smooth function. Every
  enveloping-algebra derivative of it equals the convolution of `f` with the
  same derivative of `κ`. It is derived from the real-generator version
  `compactKernelConvolutionRealDifferentiation` in
  `Langlands.Global.ArchimedeanConvolutionRealDifferentiationProof`. These
  results concern smooth kernels only. The continuous kernels quantified in
  this module's statements are not covered by them.
- `Langlands.Global.ArchimedeanGL.envelopingCompactSupport` in
  `Langlands.Global.ArchimedeanEnvelopingSupportProof` proves that enveloping
  derivatives of a compactly supported smooth function are compactly
  supported.
