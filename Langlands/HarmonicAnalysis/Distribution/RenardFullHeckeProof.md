# Renard II.3.13: proof of the full-distribution Hecke action laws

Worker 69, Task 5528. The theorem
`Langlands.HarmonicAnalysis.Distribution.RenardFullHecke.statements` proves the
published proposition
`Langlands.HarmonicAnalysis.Distribution.RenardFullHecke.Statements` at its full
universe parameter `uG`. It proves all seven conjuncts under the target's
original hypotheses: arbitrary Hausdorff, locally compact, totally disconnected
groups and any Borel left Haar measure `μ`. No countability or unimodularity is
assumed. The target pair and its imports are unchanged.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The statement's Markdown gives the locators: II.3.13, printed pp.53–55 / PDF
pp.59–61.
The route below is an internal deduction from the published Library and pinned
Mathlib. It does not transcribe the source's arguments, and the source leaves the
associativity laws as an exercise.

The module imports only the statement module and the published
`RenardUniformDensityProof`. Through that import it also uses the published
`RenardConvolutionAlgebraProof`, `RenardConvolutionDensityProof`,
`CompactSupportPairing`, `Hecke.Convolution` and `Hecke.CommonInvarianceProof`.
It introduces no new statement and no axiom.

Below, `h` also denotes the test function `Hecke.HeckeAlgebra.toTestFunction μ h`,
and `conv_ν a b` is the published `Hecke.TestFunction.convolution ν a b`, whose value is
`∫ a(y) b(y⁻¹x) dν(y)`.

## The two kernels

The published actions are defined by transposes:
`rightHeckeConvolution μ T h f = T (conv_μ f (inversion h))` and
`leftHeckeConvolution μ h T f = T (conv_{μ.inv} (inversion h) f)`.
The module names these test functions `rightKernel μ h f` and
`leftKernel μ h f`. The equalities `rightHeckeConvolution_eq_kernel` and
`leftHeckeConvolution_eq_kernel` hold by `rfl`.

- `rightKernel_apply`: `rightKernel μ a f x = ∫ a(y) f(xy) dμ(y)`. The definition
  gives `∫ f(y) a(x⁻¹y) dμ(y)`. Left invariance (Mathlib's
  `integral_mul_left_eq_self`, substituting `y ↦ xy`) turns this into the kernel.
- `integral_inv_measure`: `∫ F dμ.inv = ∫ F(y⁻¹) dμ(y)`. This follows from
  `μ.inv = map inv μ` (`Measure.inv_def`) and the measurable embedding of
  `MeasurableEquiv.inv`.
- `leftKernel_apply`: `leftKernel μ a f x = ∫ a(y) f(yx) dμ(y)`. The definition
  gives `∫ a(y⁻¹) f(y⁻¹x) dμ.inv(y)`, and `integral_inv_measure` removes the
  inversions. The left action keeps the inverted measure `μ.inv` of the
  published definition, so no unimodularity is needed.

## First conjunct: kernels (`kernel`)

The witnesses are `r = rightKernel μ h f` and `l = leftKernel μ h f`. Their
values are the two kernel identities above, and the action identities are the
`rfl` equalities. Integrability of `y ↦ h(y) f(xy)` and `y ↦ h(y) f(yx)` comes
from Mathlib's `Continuous.integrable_of_hasCompactSupport`. Each integrand is
continuous, and its support lies in the compact support of `h`.

## Second conjunct: compact compatibility (`compactCompatibility`)

The compact witness is `compactTestDensity μ h`, whose underlying distribution is
`heckeDistribution μ h` by definition.

- `rightHeckeConvolution_compact`: the published `convolution_eq_pairing`
  writes `(T * hμ)(φ)` as the compact-support pairing of `T` with
  `x ↦ ⟨hμ, y ↦ φ(xy)⟩`. The published `compactSupportPairing_testDensity`
  evaluates the inner pairing as `∫ h(y) φ(xy) dμ(y)`, which is
  `rightKernel μ h φ x`. Then `compactSupportPairing_eq_of_agrees` identifies the
  outer pairing with `T (rightKernel μ h φ)`.
- `leftHeckeConvolution_compact`: the same argument, after the published
  `compactPairing_swap` exchanges the factors of `hμ * T`. The inner pairing is
  `∫ h(x) φ(xy) dμ(x) = leftKernel μ h φ y`.

## Third conjunct: inversion (`inversionLaws`)

- `exists_inverted`: the published `RenardUniformDensity.inversion_testDensity`
  gives a test `g` with `inversion(hμ) = gμ`. This includes the modular factor.
  The witness `hi` is `g` read back in `Hecke.HeckeAlgebra μ`.
- `integral_inversion_pair`: evaluating `heckeDistribution μ hi =
  inversion(heckeDistribution μ h)` at a test `ψ` gives
  `∫ h(y) ψ(y⁻¹) dμ(y) = ∫ hi(y) ψ(y) dμ(y)`.
- `inversion_laws`: for every pair `h`, `hi` related in this way and every
  distribution `T`, both inversion laws hold. Unfolding the kernels, the first
  law requires `∫ h(y) f(y⁻¹x⁻¹) dμ(y) = ∫ hi(y) f(yx⁻¹) dμ(y)` for each `x`. This
  is `integral_inversion_pair` applied to `ψ = rightTranslate x⁻¹ f`. The second
  law requires `∫ h(y) f(x⁻¹y⁻¹) dμ(y) = ∫ hi(y) f(x⁻¹y) dμ(y)`. This is the same
  identity applied to `ψ = leftTranslate x f`.

`inversionLaws` combines `exists_inverted` with `inversion_laws`.

## Fourth conjunct: associativity (`associativity`)

All three laws reduce to identities between kernels; the identity is then
applied under `T`.

- `convolution_inversion`: `conv_μ (inversion a) (inversion b) =
  inversion (conv_μ b a)`. This is one left-invariant substitution `y ↦ x⁻¹y`.
- Right law (`rightKernel_convolution`): `rightKernel μ (h * k) f =
  rightKernel μ h (rightKernel μ k f)`. Rewrite `inversion (h * k)` with
  `convolution_inversion`, then apply the published associativity
  `Hecke.TestFunction.convolution_assoc`.
- Left law (`leftKernel_convolution`): `leftKernel μ (h * k) f =
  leftKernel μ k (leftKernel μ h f)`. Expand `(h * k)(w) = ∫ h(y) k(y⁻¹w) dμ(y)`.
  Swap the two integrals with Mathlib's
  `integral_integral_swap_of_hasCompactSupport`: the integrand is continuous,
  and its support lies in the compact set `(supp h · supp k) × supp h`.
  Substitute `w ↦ yw`, then swap again on `supp h × supp k`. Both sides become
  `∫∫ h(y) k(z) f(y(zx)) dμ(y) dμ(z)`.
- Mixed law (`rightKernel_leftKernel`): `rightKernel μ k (leftKernel μ h f) =
  leftKernel μ h (rightKernel μ k f)`. Both sides are
  `∫∫ k(z) h(y) f(yxz)` in opposite orders of integration. One compact-support
  swap on `supp k × supp h` proves the identity.

## Fifth conjunct: evaluation (`evaluation`)

The published `leftConvolveTest T φ 1` is `T (leftTranslate 1 (inversion φ))`.
The published `leftTranslate_one` simplifies this to `T (inversion φ)`. For
`φ = conv_μ h (inversion f)`, `convolution_inversion` (with
`a = inversion f`, `b = h`, and `inversion_inversion`) shows
`inversion φ = conv_μ f (inversion h) = rightKernel μ h f`.

## Sixth conjunct: inclusions (`inclusions`)

- `heckeDistributionSpace μ ≤ compactlySupported`: each `hμ` is the underlying
  distribution of the compact `compactTestDensity μ h`.
- `compactlySupported ≤ essentiallyCompact μ`: by the second conjunct, both
  actions on a compact `T` are compact convolutions, which are compactly
  supported.
- The last two inclusions are `inf_le_left` and `inf_le_right` for the defining
  infimum.

## Seventh conjunct: range preservation (`rangePreservation`)

- Left case (`left_mem_heckeDistributionSpace`): let `T` be left essentially
  compact. The published `Hecke.TestFunction.commonCompactOpenBiInvariance`
  gives a compact open subgroup `K` with `h(ky) = h(y)` for `k ∈ K`. The
  substitution `y ↦ ky` in `leftKernel_apply` makes `h · T` left
  `K`-invariant. Essential compactness makes it compactly supported, so it lies
  in `uniformCompactDistributionsLeft`. The published
  `RenardUniformDensity.uniformRange` (its second component) says that this
  space is exactly the range of `testDensity μ`. The resulting test is read
  back in `Hecke.HeckeAlgebra μ`.
- Right case (`right_mem_heckeDistributionSpace`): let `T` be right essentially
  compact. Its inversion is left essentially compact: for any `h'`, take `h''`
  with `inversion(h''μ) = h'μ` (by `exists_inverted` and involutivity). Then
  `inversion (T · h'') = h' · inversion T` by `inversion_laws`, and the published
  `inversion_mem_compactlySupported` keeps this compactly supported. By the
  left case `hi · inversion T`, which equals `inversion (T · h)`, lies in the
  Hecke range. Inversion preserves that range (`inversion_mem_heckeDistributionSpace`,
  again via `exists_inverted`), and involutivity gives the claim.

## Assembly

`statements` is the conjunction
`⟨kernel, compactCompatibility, inversionLaws, associativity, evaluation,
inclusions, rangePreservation⟩`.
