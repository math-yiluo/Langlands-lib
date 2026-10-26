# General-field rectangular, block-modulus and aggregate Haar scaling

This module proves three of the published propositions of
`Langlands/HarmonicAnalysis/GeneralHaarScalingStatement`. Each holds for every
`F : Type uF` with `[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`, including fields of positive characteristic.
The closing theorems add no hypotheses:

- `Langlands.HarmonicAnalysis.generalRectangularHaarScalingStatement` proves
  `GeneralRectangularHaarScalingStatement F`.
- `Langlands.HarmonicAnalysis.generalModulusScalingStatement` proves
  `GeneralModulusScalingStatement F`.
- `Langlands.HarmonicAnalysis.generalAdditiveHaarScalingStatement` proves the
  aggregate `GeneralAdditiveHaarScalingStatement F`.

The scalar component is the published theorem
`Langlands.HarmonicAnalysis.generalScalarHaarScalingStatement` of
`Langlands/HarmonicAnalysis/GeneralScalarHaarScalingProof`. This module imports
it unchanged and does not prove it again.

## Second countability

The determinant change-of-variables theorem `haarMeasure_map_rectangular`
assumes `SecondCountableTopology` of the field. The two reductions below
therefore take that class as a section variable. The closing theorems do not
assume it. The two component closing theorems install it locally with
`have := GeneralLocalField.secondCountableTopology F`. That published helper
derives second countability from the local-field hypotheses, through the proper
nontrivially normed field structure inducing the given topology. It is a
theorem, not a global instance. The aggregate theorem combines the three
component proofs.

## Rectangular law

`generalRectangularHaarScaling_of_scalar` takes the scalar proposition and
second countability as hypotheses. It fixes the residue normalization data
`q`, `abv` and `ϖ`, and ranks `r, s`, including zero. It equips the field with
its Borel structure, used only for an auxiliary Haar measure on `F`. It also
builds the multiplicative map `χ : F →*₀ ℝ≥0` with value `abv x`. The scalar
proposition at `addHaar` and at `Units.mk0 a ha` gives the scaling hypothesis of
`haarMeasure_map_rectangular`. That theorem is applied to the given Borel
structure and additive Haar measure on `r × s` matrices, with left matrix `A`
and right matrix `B⁻¹`. It yields the factor
`(χ (det A) ^ s * χ (det B⁻¹) ^ r)⁻¹`. This is rewritten into the published form
`(|det A|^s / |det B|^r)⁻¹` of `Shahidi.determinantAbs`. The pushforward map is
exactly `X ↦ A * X * B⁻¹`.

## Block-modulus law

`generalModulusScaling_of_rectangular` takes the rectangular proposition and
second countability as hypotheses. It keeps the positive ranks `m, n` and the
supplied Borel and `MeasurableAdd₂` premises of the target. For a Levi element
`l`, it writes `A = l 0 ∈ GL_n` and `B = l 1 ∈ GL_m`; these local definitions
avoid a dependent measurable-instance mismatch with the raw projections. On a
second-countable field the product measurable structure on `n × m` matrices is
Borel, so the rectangular law applies to `μ` with left factor `A⁻¹` and right
factor `B⁻¹`. The map becomes `X ↦ A⁻¹ * X * B`, the action in
`Shahidi.IsModulusScaling` for the swapped `(n,m)` block order. The factor
`(|det A⁻¹|^m / |det B⁻¹|^n)⁻¹` simplifies to `|det A|^m / |det B|^n`. That is
`Shahidi.leviModulus_twoBlocks` and has no outer inverse.

## Provenance and scope

Worker 99 wrote the two conditional reductions. They adapt the published p-adic
arguments `Langlands.HarmonicAnalysis.padicRectangularHaarScaling`,
`Langlands.Shahidi.map_rectangularConj_padic` and
`Langlands.PadicField.TopologicalData.isModulusScaling_padic` to the general-field
targets. They specialize the field-generic
`Langlands.HarmonicAnalysis.haarMeasure_map_rectangular`, whose module is named
`PadicRectangularHaarScalingProof`, and `Langlands.Shahidi.leviModulus_twoBlocks`.
Worker 11 added the unconditional closing theorems and the import of the
published scalar proof with its second-countability helper. The construction is
internal and has no literature source.

The module changes no published statement or imported file. It proves only
these measure-theoretic change-of-variables identities. Intertwining-integral
convergence, analytic continuation, local-coefficient existence and Shahidi's
Theorem 5.1 are outside its scope.
