# Renard II.3.13: laws of the full Hecke actions on algebraic distributions

Worker 107 and Worker 104, Task 5530. Source: Renard, *Représentations des
groupes réductifs p-adiques*, French version dated 9 July 2026, II.3.13,
Lemma and its proof, printed pp.54–55 / PDF pp.60–61, and the Theorem,
printed p.55 / PDF p.61; source registration
`renard-2026-representations-groupes-reductifs-padiques`.

This module supports the proof of
`Langlands.HarmonicAnalysis.Distribution.RenardCompletion.Statements`
in `RenardCompletionProof`. It proves helper lemmas about the published full
actions `rightHeckeConvolution μ T h` and `leftHeckeConvolution μ h T` of the
Haar Hecke algebra on all algebraic distributions, in the namespace
`Langlands.HarmonicAnalysis.Distribution.RenardCompletion`. It states no
statement-unit target. In particular, it is not a proof of the separate
full-Hecke statement units of `RenardFullHeckeStatements`: it proves only
those identities that the completion argument uses.

Throughout, `G` is a topological group with its Borel structure and `μ` is a
left Haar measure. Locally compact, Hausdorff and totally disconnected
hypotheses are added only for the lemmas that need them. No unimodularity is
assumed. As in the published definitions, `T*h` is the transpose of the test
operator `f ↦ f * ȟ`, a left-Haar convolution, and `h*T` is the transpose of
`f ↦ ȟ * f`, where that convolution uses the inverse measure `μ.inv`. Here
`ȟ(x) = h(x⁻¹)` is the bare function inversion.

## Test-function identities

- `convolution_inversion_apply`: `(f * ȟ)(x) = ∫ f(xy) h(y) dμ(y)`, by the left
  invariance of `μ` under `y ↦ xy`.
- `inversion_convolution`: `(h * k)ˇ = ǩ * ȟ` for left-Haar convolution of
  tests. The proof again uses only left invariance, so it holds without
  unimodularity.
- `rightTest_assoc`: `(f * ǩ) * ȟ = f * (h * k)ˇ`. This follows from the
  published associativity of test convolution and the previous identity.
- `convolution_inv_apply`: `(ȟ *_{μ.inv} f)(x) = ∫ h(y) f(yx) dμ(y)`. This uses
  the definition of `μ.inv` as the image of `μ` under inversion.
- `leftTest_rightTest_comm`: the test operators of the left and right actions
  commute, `(ȟ *_{μ.inv} f) * ě = ȟ *_{μ.inv} (f * ě)`. Both sides equal
  `∫∫ h(y) f(yxz) e(z) dμ(y) dμ(z)`. The two iterated integrals are exchanged
  with `integral_integral_swap_of_hasCompactSupport`, since the integrand is
  continuous with support in the compact product of the supports of `e` and `h`.

## Laws of the full actions

- `rightHeckeConvolution_mul`: `(T*h)*k = T*(h*k)` for every distribution `T`.
  This is `T` applied to `rightTest_assoc`.
- `leftHecke_rightHecke_comm`: `h*(T*e) = (h*T)*e` for every distribution `T`.
  This is `T` applied to `leftTest_rightTest_comm`.

## Actions on Hecke densities

`heckeDistribution μ k` is the published density `f ↦ ∫ k f dμ`.

- `heckeDistribution_apply_eq_convolution`: `∫ k f dμ = (k * f̌)(1)`.
- `rightHeckeConvolution_heckeDistribution`: `(k μ)*h = (k*h) μ`. It follows from
  the previous formula, `inversion_convolution`, double inversion and
  associativity of test convolution.
- `leftHeckeConvolution_heckeDistribution`: `h*(k μ) = (h*k) μ`. It is proved by
  `convolution_inv_apply` and two exchanges of iterated integrals over compactly
  supported continuous integrands, with the left-invariant change of variable
  `x ↦ yx` between them.
- `rightHeckeConvolution_dirac_one`: `δ₁ * h = h μ`, directly from
  `convolution_inversion_apply`.

These are the source's statements that the actions of `H(G)` on distributions
extend the Hecke product, and that `δ₁` is neutral.

## Kernel, faithfulness and essential compactness

These lemmas assume in addition that `G` is Hausdorff. All except the kernel
formula also assume that `G` is locally compact and totally disconnected.

- `rightHeckeConvolution_apply_eq_integral`: for every algebraic distribution `D`,
  `(D*h)(f) = ∫ x ↦ D(y ↦ h(y⁻¹x)) · f(x) dμ(x)`. In the published notation, the
  kernel is `leftConvolveTest D h`. The test `f * ȟ` is rewritten as the partial
  integral of the compact kernel `leftDensityChangedKernel h f`. The published
  exchange `distribution_partialIntegral`, from `RenardConvolutionDensityProof`,
  then moves `D` inside the integral. Each slice of the kernel is
  `f(x) · (y ↦ h(y⁻¹x))`. No topology on the algebraic dual is used.
- `heckeDistribution_injective`: `k ↦ k μ` is injective. This is the published
  `RenardHaar.density_injective` applied to the underlying locally constant
  functions.
- `rightHeckeConvolution_compact`: for a compactly supported distribution `T`,
  the full action `T*h` is the published compact convolution of `T` with the test
  density of `h`. The proof combines the kernel formula with
  `convolution_testDensity_left`.
- `exists_heckeDistribution_eq`: if `T` is right essentially compact, then for
  every `h` there is a Hecke element `k` with `k μ = T*h`. The kernel formula
  writes `T*h` as the density of the locally constant function
  `leftConvolveTest T h`, by the published `leftConvolveTest_locallyConstant`.
  The published `RenardHaar.density_support` identifies the support of that
  function with the support of `T*h`, which is compact by hypothesis. The
  function is therefore a test function. This is the source's remark before the
  Lemma that `T*h ∈ H(G)` (printed p.54), proved elementwise.
- `compact_mem_rightEssentiallyCompact`,
  `heckeDistribution_mem_rightEssentiallyCompact` and
  `dirac_one_mem_rightEssentiallyCompact`: compactly supported distributions,
  Hecke densities and `δ₁` are right essentially compact. They follow from
  `rightHeckeConvolution_compact`, `rightHeckeConvolution_heckeDistribution` and
  `rightHeckeConvolution_dirac_one`, with the published compact support of
  compact convolutions and of test densities.

All auxiliary names are internal helper lemmas derived from the published
definitions and the integral formulas above.
