# Restricting a compatible measure to a compact-open orbit

Author: Worker 659. Worker 88 supplied the proof route in the task context.

`Langlands.QuotientIntegration.compactOpenOrbitMeasure` proves exactly the
published `Langlands.QuotientIntegration.CompactOpenOrbitMeasureStatement`.
Its complete type is that proposition, with its arbitrary universe and every
original hypothesis retained. This module adds a proof and reusable intermediate
lemmas; it changes neither the statement pair nor any imported published pair.

The provenance is internal: the proof derives the formula from the actual
compact-continuous complex Weil identity in `IsCompatible`, the published
quotient topology, and pinned Mathlib measure integration and regularity.
It makes no separate external theorem claim. `QuotientFunctional` supplies the
import of real compact-continuous regular-measure extensionality; its averaging
construction is not an additional input to this proof.

For a compact open subgroup `K` and `g : G`, write

```text
q(x) = leftQuotientMap H x
A = {x | g⁻¹ x ∈ K} = gK
C = {q(gk) | k ∈ K}
S = {h : H | g⁻¹ h g ∈ K}
c = μH S
κ = μG.restrict K.
```

The theorem proves `0 < c`, `c < ∞`, and the equality of actual measures

```text
μ.restrict C = c⁻¹ • Measure.map (fun k => q (g * k)) κ.
```

The inverse and scalar action in this formula are those of `ℝ≥0∞`. The actual
mass `μG K` is retained throughout; no unit-mass premise is introduced. Neither
normality of `H` nor right invariance of `μG` is required. No quotient-measure
existence premise, disintegration, averaging formula or desired equality is
added: `μ` is any actual measure satisfying the published `IsCompatible`.

The implementation first proves `leftQuotientMap_subgroup_mul`. Consequently,
`quotientAverage_pullback_mul` factors a pulled-back quotient function out of
the actual Bochner subgroup integral. The identity uses the total integral's
constant-multiplication theorem, so it needs no additional integrability premise.

`isOpen_compactOpenOrbitStabilizer` expresses `S` as the continuous preimage
of `K`. For `isCompact_compactOpenOrbitStabilizer`, the inclusion of the closed
subgroup `H` is a closed embedding, and composing it with conjugation remains
a closed embedding. The compact preimage theorem gives compactness of `S`.
It contains the identity. Positivity of Haar measure on nonempty open sets
and finiteness of a regular Haar measure on compact sets therefore give
`0 < c < ∞`.

`quotientAverage_compactOpen_leftCoset_indicator` computes the average of
`1_A` on the actual quotient. A point of `C` has a representative `gk`, with
`k ∈ K`. The condition `h g k ∈ gK` is equivalent to `g⁻¹ h g ∈ K`, since
right multiplication by `k` preserves membership in the subgroup `K`. Thus
the fiber indicator integrates to `(c.toReal : ℂ)`. Outside `C`, every fiber
indicator is zero: any nonzero value would supply a representative in `gK`.
The result is precisely `C.indicator (fun _ => (c.toReal : ℂ))`.

`quotientAverage_compactOpen_leftCoset_pullback` combines that calculation
with the pullback factorization. For any complex quotient function `φ`, the
average of `A.indicator (φ ∘ q)` is
`C.indicator (fun z => (c.toReal : ℂ) * φ z)`. This shared helper is proved
using the actual `quotientAverage` API. Right invariance of `μH` is exactly
the orientation already used by that API to descend the integral
`h ↦ f(h x)` to left cosets `H x`.

`IsCompatible.integral_compactOpenOrbit` applies the Weil identity to the
complexification of a continuous real quotient function pulled back to the
group and cut off on `A`. The set `A` is compact and clopen, so this is a
continuous compactly supported ambient test even when the original quotient
function has no compact support. The computed average and the unconditional
complexification identity for Bochner integrals give a real identity. Ambient
left Haar invariance, by the substitution `x = gk`, yields

```text
c.toReal * ∫ z in C, φ z ∂μ = ∫ k in K, φ (q (gk)) ∂μG.
```

Finally, the quotient is Hausdorff and locally compact by the published
topology lemmas. The restrictions to `C` and `K` have finite mass and are
regular. The continuous pushforward of `κ` is finite and inner regular,
hence regular on the Hausdorff quotient. The measure `c • μ.restrict C` is
regular because `c` is finite. Testing these last two measures on all real
compactly supported continuous functions and using the integral identity
proves

```text
c • μ.restrict C = Measure.map (fun k => q (g * k)) κ.
```

Scalar associativity and the extended-nonnegative-real identity
`c⁻¹ * c = 1`, justified by positivity and finiteness, give the target equality.
This proves a restriction formula; no downstream GL application is asserted.
