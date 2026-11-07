# Self-dual measures for a scaled additive character

Lean module: `Langlands.Representation.RankinSelberg.PairFactorCharacterChangeMeasures`.

This is a helper module for the proof of
`Langlands.RankinSelberg.PairFactorCharacterChangeStatement`. It proves the
standard fact from Tate's local harmonic analysis: if `ψ^a(x) = ψ(a x)`, the
measure self-dual for `ψ^a` is `|a|^(1/2)` times the measure self-dual for `ψ`.
The proof below is an internal derivation from the Library's definitions
(`IsSelfDual`, `fourierTransform`, `fourierIntegral`) and from the Library's
p-adic Haar scaling and Fourier duality theorems; no literature argument is
formalized step by step.

## Generic declarations (namespace `Langlands.HarmonicAnalysis`)

These hold for a field `K` with a topological ring structure and a Borel
measurable structure; the last one also needs `K` locally compact, Hausdorff
and totally disconnected.

- `fourierIntegral_scale`: for a unit `a`,
  `fourierIntegral (ψ.scale a) μ G y = fourierIntegral ψ μ G (a * y)`.
  Proof: the integrands agree pointwise, since `ψ(a (x y)) = ψ(x (a y))`.

- `fourierIntegral_scale_measure`: for `c > 0`,
  `fourierIntegral ψ (μ.scale c hc) G y = c * fourierIntegral ψ μ G y`.
  Proof: `AdditiveHaarMeasure.scale_measure` and `integral_smul_nnreal_measure`.

- `integral_comp_mul_left_of_map`: if the pushforward of `μ` under `x ↦ a x`
  is `d • μ`, then `∫ h(a x) dμ = d * ∫ h dμ`. Proof: `x ↦ a x` is a
  measurable embedding (`Homeomorph.mulLeft₀`), so
  `MeasurableEmbedding.integral_map` rewrites the left side as an integral
  against the pushforward, which is `d • μ`.

- `integrable_comp_mul_left_of_map`: under the same hypothesis, integrability of
  `h` gives integrability of `x ↦ h(a x)`
  (`MeasurableEmbedding.integrable_map_iff`).

- `IsSelfDual.scale_of_map`: if `μ` is self-dual for `ψ` and the pushforward of
  `μ` under `x ↦ a x` is `(c^2)⁻¹ • μ` with `c > 0`, then `c • μ` (that is,
  `μ.scale c hc`) is self-dual for `ψ.scale a`. Proof: by the two previous
  scaling lemmas the transform for `(ψ.scale a, c μ)` is
  `x ↦ c * F f (a x)`, where `F` is the transform for `(ψ, μ)`. The integrand of
  the second transform is then `c` times a function of `a x`, so its
  integrability follows from `integrable_comp_mul_left_of_map`, and by
  `integral_comp_mul_left_of_map` the double transform at `y` equals
  `c * c * (c^2)⁻¹ * F(F f)(y) = f(-y)`, using the self-duality of `μ`.

## p-adic declarations (namespace `Langlands.LocalFactor.PadicAbelian`)

These are for a p-adic field `F` with its canonical topological data, Borel
measurable structure and the induced local-field instances.

- `sqrtNormalizedAbs F a`: the nonnegative real `|a|^(1/2)`, the square root of
  the residue-normalized absolute value of the unit `a`
  (`normalizedAbsUnits`). `sqrtNormalizedAbs_pos` shows it is positive and
  `sqrtNormalizedAbs_sq` shows its square is `normalizedAbs a`.

- `isSelfDual_scale`: for every `ν : SelfDualHaar _ ψ`, the measure
  `ν.val.scale (sqrtNormalizedAbs F a) _` is self-dual for `ψ.scale a`. Proof:
  `IsSelfDual.scale_of_map`, with the pushforward hypothesis supplied by
  `padicScalarHaarScaling` (multiplication by `a` pushes a Haar measure
  forward to `|a|⁻¹` times itself).

- `SelfDualHaar.val_eq_scale`: for `ν : SelfDualHaar _ ψ` and
  `ν' : SelfDualHaar _ (ψ.scale a)`,
  `ν'.val = ν.val.scale (sqrtNormalizedAbs F a) _`. Proof: the uniqueness
  clause of `LocalFactors.padicFourierDuality` for the nontrivial character
  `ψ.scale a`, applied to `ν'.val` and the measure of `isSelfDual_scale`.
