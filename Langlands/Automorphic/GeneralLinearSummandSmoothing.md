# Archimedean smoothing of a continuous quotient class

Module `Langlands.Automorphic.GeneralLinearSummandSmoothing`. It concerns the positive-central
rational quotient `Q` of `GL_{r+1}` over a number field `F`, with its canonical quotient Haar
measure `μQ`. A continuous function on `Q` is convolved in the archimedean variable with a
smooth compactly supported kernel. The module identifies the result as a finite-smooth
rational function and computes its enveloping derivatives. It also identifies the `L²` classes
of these derivatives and their derivatives along real exponential curves.

## Definitions

- `archimedeanAdelicPoint F r`: the continuous inclusion of `GL_{r+1}(F ⊗ ℝ)`
  (`InfiniteAdelicGL`) into the group-scheme adelic points, through `AdelicGL.ofInfinite` and
  the inverse of `GeneralLinearGroupPoints.adelicHomeomorph`.
- `smoothingWeight F r D κ`: the continuous weight `z ↦ (D κ)(z⁻¹)` for an element `D` of the
  enveloping algebra and a kernel `κ : ArchimedeanGL.SmoothCompactKernel`. Here `D κ` is the
  Library's `ArchimedeanGL.envelopingAction`. `smoothingWeight_hasCompactSupport` uses
  `envelopingCompactSupport`.
- `smoothedQuotientFunction F r T i ν D κ h`: for a Haar measure `ν` on `InfiniteAdelicGL` and
  `h : C(Q, ℂ)`, the function `q ↦ ∫ (D κ)(z⁻¹) h(q z) dν(z)`. This is
  `weightedQuotientOrbitIntegral` with the above weight.
- `smoothedClass F r T i ν hi I e hc D κ u`: the Bochner integral
  `∫ (D κ)(z⁻¹) • ρ(z) u dν(z)` of the archimedean orbit of a class `u` in `L²(Q, μQ)`. Here
  `ρ` is `haarQuotientL2BoundedRightAction`.

## Results

- `evaluate_pullback`: the matrix-model function of the pullback of `k : C(Q, ℂ)` takes at `g`
  the value of `k` at the coset of the group-scheme point of `g`.
- `evaluate_smoothedQuotientFunction`: at the point with archimedean coordinate `a` and finite
  coordinate `b`, the pullback of `smoothedQuotientFunction … D κ h` equals
  `∫ s_b(y) (D κ)(y⁻¹ a) dν(y)`, where `s_b(y)` is the value of the pullback of `h` at the
  point `(y, b)`. The proof substitutes `y = a z`, using left invariance of `ν`.
- `smoothedQuotientFunction_rightTranslate_finite`: if `h` is invariant under right
  translation by a subgroup `L` of the finite adelic group, so is every smoothed function.
  Finite and archimedean translations commute (`ofFinite_mul_ofInfinite`).
- `exists_finiteSmooth_smoothing`: suppose `h` is right-invariant under an open subgroup `L` of
  the finite adelic points.
  Then there is `f : FiniteSmoothRationalFunctions F (r+1)` with
  `finiteSmoothEnvelopingAction D f` equal to the pullback of
  `smoothedQuotientFunction … D κ h` for every `D`. For each finite coordinate, the slice
  formula exhibits the slice as the Library's `ArchimedeanGL.rawConvolution` of a continuous
  function with `κ`. `ArchimedeanGL.compactKernelConvolutionDifferentiation` makes it smooth,
  with `D` acting on the kernel. Invariance under `L` gives an open stabilizer in the finite
  adelic group.
- `integrable_smoothingOrbit` and `isGeneralLinearFormClass_smoothedClass`: if `h` represents
  `u` almost everywhere, the weighted orbit is integrable. The smoothed class is then the form
  class (`IsGeneralLinearFormClass`) of the pullback of the smoothed function. Both come from
  the Library's `groupSchemeQuotientL2IntegratedRepresentative`.
- `smoothedClass_mem`: a closed submodule of `L²(Q, μQ)` invariant under `ρ` contains the
  smoothed classes of its vectors (`integral_mem_of_isClosed`).
- `hasDerivAt_smoothedClass`: under the hypotheses of `exists_finiteSmooth_smoothing`, take a
  real direction `X` and the generator `X̃` of the enveloping algebra it defines. Then the
  orbit of `smoothedClass … D κ u` along the real exponential curve of `X` has derivative at
  `0` equal to `smoothedClass … (X̃ * D) κ u`. The proof applies the Library's
  `GeneralLinearFormClassDerivative.quotient_hasDerivAt_of_formClasses` to the finite-smooth
  function `finiteSmoothEnvelopingAction D f` and its two form classes.

## Provenance

These are internal steps of the Library's construction of nonzero forms attached to an
irreducible cuspidal summand, in `Langlands.Automorphic.GeneralLinearSummandFormsNonzero`. In Getz
and Hahn, *An Introduction to Automorphic Representations* (2024), Lemma 9.7.2, printed
pp. 264–265 (PDF pp. 276–277), writes every `K`-finite vector `φ` of an irreducible unitary
representation as `π(f)φ` with `f` smooth and compactly supported. At the archimedean place it
uses Proposition 4.5.6, printed p. 123 (PDF p. 138). Here an arbitrary continuous representative
is smoothed by a smooth compactly supported archimedean kernel instead. The pointwise
convolution formulas follow the Library's differential stability proof
`generalLinearClosedFormClassesEnveloping` in
`Langlands.Automorphic.GeneralLinearSummandFormsEnveloping`. There the kernel reproduces an
existing form; here it smooths an arbitrary continuous representative. The module proves no
growth, compact finiteness, centre finiteness or cuspidality.
