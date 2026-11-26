# Small right oscillation of compact convolution

This module proves a uniform estimate for the right oscillation of a
compact convolution on the positive rational quotient. The notation `A`,
`Γ`, `Q`, `μQ` and `R f hf` is that of `GroupSchemeQuotientL2CompactPart`:
the full adelic group, the positive rational subgroup, the quotient, its
Haar measure, and the integrated right action of a weight for the left
Haar measure of `A`. Write `q · a` for
`LeftCosetSpace.rightTranslate Γ a q`.

## Statement

`exists_positiveQuotientL2ConvolutionOscillation`: for `f : C_c(A, ℂ)`
there is a constant `C ≥ 0` with the following property. For every
`ε > 0` there is a neighborhood `U` of `1` in `A` such that, for every
`φ ∈ Lp ℂ 2 μQ`, there are a continuous `ψ : Q → ℂ` and a class `B` with

- `R f hf φ = ψ` almost everywhere,
- `‖B‖ ≤ C · ‖φ‖`, and
- for almost every `q` and every `a ∈ U`,
  `‖ψ q - ψ (q · a)‖ ≤ ε · ‖B q‖`.

The constant `C` does not depend on `ε` or `φ`, and `U` does not depend
on `φ`.

## Proof

A private lemma, `exists_translation_envelope`, works on any locally
compact Hausdorff topological group `H`. For `f : C_c(H, ℂ)` it gives a
nonnegative `b : C_c(H, ℝ)` such that for every `ε > 0` some neighborhood
`U` of `1` satisfies `‖f g - f (a⁻¹ g)‖ ≤ ε · b g` for all `a ∈ U` and all
`g`. Choose a compact neighborhood `V` of `1` and let `b` be an Urysohn
function (`exists_continuous_one_zero_of_isCompact`) with values in
`[0, 1]` and compact support, equal to `1` on the compact set
`V · tsupport f ∪ tsupport f`. Uniform continuity of `g ↦ f g⁻¹`, from
`OperatorRealization.exists_nhds_one_norm_sub_lt`, gives the estimate on
that set. Outside it both `f g` and `f (a⁻¹ g)` vanish for `a ∈ V`.

For the main statement, take the continuous rows `k` of `f` from
`exists_positiveQuotientL2ConvolutionRows` and set `ψ q = ⟪k q, φ⟫`.
Let `b` be the envelope of `f`, regarded as a complex weight, and set
`C = ∫ ‖b‖`. Let `|φ|` be the `L²` class of `q ↦ ‖φ q‖` and
`B = R b hb |φ|`. Then
`‖B‖ ≤ ‖R b hb‖ · ‖|φ|‖ ≤ C · ‖φ‖` by
`norm_haarQuotientL2IntegratedAction_le`.

At a representative `x` of `q`, the row formula and left invariance of
Haar measure (`integral_mul_left_eq_self`) give
```
ψ [x] - ψ [x a] = ∫ (f g - f (a⁻¹ g)) · φ [x g] dg.
```
The envelope bounds the norm of the right side by
`ε · ∫ b g · ‖φ [x g]‖ dg`. The rows of `b` evaluate this last integral
as `‖B [x]‖`, for almost every `[x]`. This step uses that the
representative of `|φ|` agrees with `‖φ‖` almost everywhere along almost
every right translate. That follows from quasi-measure preservation of
the right translations (`haarQuotientMeasureRightInvariant`) and the
exchange of almost-everywhere quantifiers `Measure.ae_ae_comm`, with
measurability from `continuous_positiveQuotient_rightTranslate`.

## Provenance

This is the standard estimate obtained from the uniform continuity of a
compactly supported weight. Its quotient form is internal to this
Library: it provides the oscillation bound used together with
`exists_compact_cuspDisplacementCover` in
`generalLinearFullAEL2CuspidalCompactness`.
