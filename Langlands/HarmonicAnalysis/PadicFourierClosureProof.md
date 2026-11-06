# Scalar p-adic Fourier closure for every supplied Haar measure

Author: Worker 1679.

`Langlands.HarmonicAnalysis.padicFourierClosure.{u}` proves exactly
`Langlands.LocalFactors.PadicFourierClosureStatement.{u}` from
[the published target](../LocalFactor/Harmonic/Statement.md).
The theorem has no outer parameters or additional hypotheses:

```lean
theorem Langlands.HarmonicAnalysis.padicFourierClosure :
    Langlands.LocalFactors.PadicFourierClosureStatement.{u}
```

It covers every prime, every `F : PadicField.{u} p` in arbitrary carrier
universe `u`, every supplied `T : F.TopologicalData`, every continuous
nontrivial Circle-valued additive character `ψ`, every actual Borel additive
Haar measure `μ`, and every raw complex function `f` that is locally constant
and compactly supported. It proves integrability of `f`, integrability of
every Fourier integrand, equality of `Fourier.fourierIntegral ψ⁻¹ μ f` with
the plus-sign Bochner integral, and local constancy, compact support and
integrability of that transform.

## Supplied topology and actual measure

The proof installs `T.topology`, `T.valuativeRel` and `T.localField`.
The additive group's right uniformity and its compatible
`IsUniformAddGroup` certificate retain this topology. The measurable space
is its Borel space. The published `T.fieldT2` supplies Hausdorffness.

The published
[`padicSelfDualMeasureExists`](PadicSelfDualMeasureExistsProof.md)
supplies a total-disconnectedness certificate and self-dual existence for
each actual character in this topology. The given character is packaged
without alteration as `χ : UnitaryAdditiveCharacter F.Carrier`.

The given `μ` is packaged without alteration as
`ν : AdditiveHaarMeasure F.Carrier`. The regularity field is proved by
`T.haarMeasure_regular μ` from
[PadicScalarHaarScalingProof](PadicScalarHaarScalingProof.md).
That published theorem derives regularity from sigma compactness and
pseudometrizability of the supplied topology and local finiteness of Haar
measure. No regularity or measure normalization is added to the target's
hypotheses.

## Implemented closure argument

Choose a self-dual witness `σ` using `padicSelfDualMeasureExists`.
The published
[`compactOpenAnnihilator`](CompactOpenAnnihilatorProof.md), applied to
`χ` and `σ`, proves compactness of

```text
{y | for every x in H, χ.complex (x*y) = 1}
```

for each compact open additive subgroup `H`. This conclusion involves only
the character and the subgroup. The proof then supplies it to the published
[`scalarFourierClosed_of_compactAnnihilator`](ScalarFourierClosureProof.md),
applied to `χ`, the original measure bundle `ν`, and
`φ = ⟨f, hfl, hfc⟩ : SchwartzBruhat F.Carrier`.
This yields an actual Schwartz–Bruhat function `g` pointwise equal to
`fourierIntegral χ ν f`.

The imported closure helper proves local constancy using local constancy
of the continuous character and compactness of the support of the input.
It proves compact support by choosing a compact open subgroup fixing the
input under translation and placing the transform's support inside that
subgroup's compact annihilator. Only the annihilator compactness argument
uses `σ`; every Fourier integral in the conclusion uses the supplied `μ`.
Self-duality of `μ` is never assumed or asserted.

## Integral convention and convergence

Mathlib's `Fourier.fourierIntegral ψ⁻¹ μ f y` has kernel
`ψ⁻¹ (-(x*y)) • f x`. `AddChar.inv_apply` cancels the two minus signs,
and `Circle.smul_def` identifies the circle action with multiplication by
its complex coercion. The local identity `hplus` is therefore

```text
Fourier.fourierIntegral ψ⁻¹ μ f y
  = ∫ x, (ψ (x*y) : ℂ) * f x ∂μ.
```

This is the same plus-sign integral as `fourierIntegral χ ν φ`.
Combining `hplus` with the pointwise equality for `g` gives the exact
function equality `htransform`, with no almost-everywhere replacement.

Local constancy makes `f` continuous. Mathlib's
`Continuous.integrable_of_hasCompactSupport` proves integrability of `f`
for the locally finite Haar measure `μ`.
The published `fourierIntegrand_integrable χ ν φ y` from [Basic](Basic.md)
proves integrability of the continuous compactly supported function
`x ↦ (ψ (x*y) : ℂ) * f x` for every `y`.
Finally, `htransform` transports local constancy and compact support from
`g` to the requested Mathlib transform. The same continuous compact-support
integrability theorem proves integrability of that transform against `μ`.
All convergence clauses are explicit conclusions.

## Provenance and scope

This is an internal derivation from the unchanged published target and
proof APIs listed above, together with Mathlib's Fourier definition and
compact-support integration. It introduces no new mathematical object or
source assertion. The target's paired Markdown records its original
Weil, Tate and Deligne correspondence and the plus-sign convention.
The imported self-dual existence theorem derives its witness from the
published valuation-lattice Haar masses, lattice Fourier formulas and
finite Schwartz–Bruhat expansions.

The scalar-ratio correction documented in the target uses the positive
exponent for the fixed-Haar to self-dual ratio. This proof requires no
ratio formula or rescaling of the supplied measure.
The other duality, scaling, conductor and normalization targets in the
same statement module remain separate propositions.
