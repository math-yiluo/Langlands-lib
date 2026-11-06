# Dual Haar measures and scalar Fourier inversion

Author: Worker 135.

The theorem `Langlands.LocalFactors.padicFourierDuality.{u}` proves the
unchanged published proposition
`Langlands.LocalFactors.PadicFourierDualityStatement.{u}` from
[Statement](Statement.md). Its complete declaration is

```lean
theorem Langlands.LocalFactors.padicFourierDuality :
    Langlands.LocalFactors.PadicFourierDualityStatement.{u}
```

In particular, the theorem covers every prime, every field universe `u`,
every `F : Langlands.PadicField p`, and every supplied
`T : F.TopologicalData`. It adds no hypotheses to the target. Total
disconnectedness, self-dual existence, raw inversion for the dual witness,
all uniqueness assertions, the bundled/raw equivalence, and symmetry are
proved conclusions.

## Objects and dependencies

All measures and integrals use the Borel measurable space of `T.topology`.
The proof installs the valuative relation and local-field structure of `T`,
the right additive uniformity, and its uniform-additive-group certificate,
as the target requires.

The already published
`Langlands.HarmonicAnalysis.padicSelfDualMeasureExists F T` in
[PadicSelfDualMeasureExistsProof](../../HarmonicAnalysis/PadicSelfDualMeasureExistsProof.md)
provides the total-disconnectedness certificate. For each given continuous
nontrivial character `ψ`, bundled as `χ : UnitaryAdditiveCharacter`, it
also provides a regular additive Haar measure `σ` and a proof of
`IsSelfDual χ σ`. Thus the reference measure is obtained from a proved
existence theorem before any test function is considered.

The supplied topology is second countable by
`T.secondCountableTopology`, imported transitively from
[PadicScalarHaarScalingProof](../../HarmonicAnalysis/PadicScalarHaarScalingProof.md).
Consequently, every raw additive Haar measure in the target is regular,
so Mathlib's Haar uniqueness theorem applies to it. Bundled
`AdditiveHaarMeasure` values already include regularity.

The compactness and openness results `T.isCompact_integers` and
`T.isOpen_integers` in the same module show that the actual integer
subring is compact and clopen. The proof uses
`Langlands.Hecke.TestFunction.characteristic` from
[TestFunction](../../Representation/Hecke/TestFunction.md) to form its
Schwartz–Bruhat characteristic function `g`. Since zero belongs to the
integer subring, `g 0 = 1`.

## Implemented comparison proof

For this paragraph, write

```text
Fμ(f)(y) = Fourier.fourierIntegral χ.toAddChar⁻¹ μ f y.
```

The private lemma `plusFourier_eq_integral` rewrites Mathlib's transform
as `∫ x, χ.complex (x*y) * f x ∂μ`. Mathlib's minus sign is cancelled
by the inverse character, so this is exactly the plus-sign convention of
the existing harmonic module.

The lemmas `plusFourier_smul_measure` and `plusFourier_const_mul` prove

```text
F(c • μ)(f)(y) = (c : ℂ) * Fμ(f)(y),
Fμ(a * f)(y) = a * Fμ(f)(y),
```

where `c : NNReal` and `a : ℂ`. They use
`integral_smul_nnreal_measure` and `integral_const_mul`. These algebraic
identities hold for Mathlib's totalized integral without an integrability
premise. Integrability needed for the bundled predicate is established
separately below.

The internal proposition `RawDual χ μ ν` abbreviates exactly the target's
raw reflection equation, quantified over all locally constant compactly
supported complex-valued functions and all arguments. The lemma
`selfDual_raw` identifies the reflection clause of `IsSelfDual` with that
equation.

Combining the two scaling identities with the known self-duality of `σ`
gives `doubleFourier_scaled`:

```text
F(d • σ.measure)(F(c • σ.measure)(f))(x)
    = ((d*c : NNReal) : ℂ) * f(-x).
```

This holds for every test function `f`. Evaluating the raw reflection
equation at the test function `g` and at zero forces `d*c = 1`, since
`g 0 = 1`. Conversely, that scalar equality makes the displayed double
transform equal to reflection for every test function. This is
`rawDual_scaled_iff`.

## Convergence and the bundled equivalence

The forward direction of `isSelfDual_iff_raw` is `selfDual_raw`. For the
reverse direction, let `μ` be any regular bundled additive Haar measure.
Mathlib's `Measure.isAddLeftInvariant_eq_smul_of_regular` gives

```text
μ.measure = c • σ.measure,
c = μ.measure.addHaarScalarFactor σ.measure : NNReal.
```

Its first Fourier transform is therefore `c` times that for `σ`. For
every test function and every second-transform argument, the second
integrand for `σ` is integrable by `IsSelfDual χ σ`. Multiplication by
the constant `c` preserves integrability, and
`Integrable.smul_measure_nnreal` transfers it to the measure `c • σ`.
An everywhere pointwise equality identifies the resulting integrand
with the required one for `μ`.

This proves convergence independently of the supplied raw equation.
That equation then supplies the reflection clause. Hence the raw
equation is equivalent to the full `IsSelfDual` predicate, including
its second-integrand convergence requirement; convergence is not inferred
from a totalized integral equality.

## Existence, uniqueness, and symmetry

For an arbitrary fixed raw additive Haar measure `μ`, Mathlib's
`Measure.isAddLeftInvariant_eq_smul` writes it as `c • σ.measure`.
The lemma
`Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure` gives `c > 0`.
The dual witness in `rawDual_existsUnique` is the actual measure

```text
ν = c⁻¹ • σ.measure.
```

It is an additive Haar measure by
`Measure.IsAddHaarMeasure.nnreal_smul`, since the inverse scalar is
nonzero. The equation `c⁻¹*c = 1` and `rawDual_scaled_iff` prove raw
inversion for this witness on every test function.

If another additive Haar measure is `d • σ.measure` and is dual to `μ`,
the same equivalence gives `d*c = 1`. Cancellation of the nonzero `c`
yields `d = c⁻¹`, and hence equality of the actual measures. This
proves the target's `∃!` for every fixed `μ`.

For bundled self-dual uniqueness, `selfDual_eq` writes a self-dual `μ`
as `c • σ.measure`. Its raw equation forces `c*c = 1`.
The injectivity of squaring on nonnegative elements, expressed by
`mul_self_inj`, gives `c = 1`. Thus its underlying measure equals
`σ.measure`, and proof irrelevance gives equality of the Haar bundles.
Applying this to each of the target's two bundles proves their equality.

Finally, if `μ = c • σ.measure` and `ν = d • σ.measure` are dual,
then `d*c = 1`. Commutativity gives `c*d = 1`, which proves reversed
duality by `rawDual_scaled_iff`. This is `rawDual_symm`.
The final theorem assembles these conclusions with the self-dual
existence witness.

## Provenance and verification boundary

This is a derived assembly proof from the published self-dual existence
theorem, supplied-topology lemmas, and Mathlib's positive proportionality
of Haar measures. The private comparison lemmas are internal consequences
of those results and the actual Bochner integral; they are not new
assumptions or external mathematical interfaces.

The original-source correspondence and Fourier conventions are those
documented in [Statement](Statement.md), notably Weil's *Basic Number
Theory*, Chapter VII §2, pp.104–108. This implementation derives uniqueness
and the dual measure by scalar comparison with the already constructed
self-dual measure. It does not introduce a new local-factor theorem or
assert the other components of `PadicHarmonicAnalysisStatement`.
The target pair and all existing imported pairs are unchanged.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation and a Lake build with declaration inspection
succeeded with no errors or warnings. Inspection reports the single
universe parameter `u` and only `propext`, `Classical.choice`, and
`Quot.sound`. Exact-target validation, independent semantic acceptance,
and Library publication remain separate submission requirements.
