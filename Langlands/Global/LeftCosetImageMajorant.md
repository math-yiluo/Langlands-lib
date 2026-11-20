# Integrable majorants on `Γ \ H` from images of compact sets

This module contains general measure theory on the left coset space `Γ \ H` (`LeftCosetSpace Γ`)
of a discrete subgroup `Γ` of a topological group `H`. It is the measure-theoretic half of the
reduction of MW II.1.6 (i) to MW II.1.5 (Mœglin–Waldspurger, *Spectral decomposition and
Eisenstein series*, printed p. 88). There, a summable bound on the cosets of a discrete group is
turned into an integrable bound on a quotient.

Provenance: these are internal lemmas, derived directly from the Library's
`LeftCosetSpace.quotientMeasure`, `discreteQuotientMeasure` and `isFundamentalDomain`
(`Langlands.Global.LeftCosetFundamentalDomain`), and from Mathlib's measure theory. No
literature result is transcribed.

Standing assumptions from `measurableSet_mk_image` onward: `H` is a Hausdorff topological group
with its Borel σ-algebra. For the integrability results, `H` is also second countable.

## Images of sets

- `preimage_image_mk Γ B`: for any subgroup `Γ` of a group `H`, the preimage in `H` of the image
  of `B` in `Γ \ H` is `⋃_{γ ∈ Γ} γ B`.
- `measurableSet_mk_image`: for countable `Γ` and compact `B`, the image of `B` in `Γ \ H` is
  measurable. By the previous item, its preimage is a countable union of compact, hence closed,
  translates.
- `quotientMeasure_mk_image_le`: let `ν` be a `Γ`-invariant measure on `H` and `s` a fundamental
  domain for `Γ`. If the image of `B` is measurable, its quotient measure is at most `ν B`. The
  quotient measure is `ν(⋃_γ γB ∩ s)`. Fundamental domains give `ν B = ∑_γ ν(γB ∩ s)`, and the
  bound is countable subadditivity.

## The majorant

- `imageIndicatorSum Γ B β` (definition): for a family of sets `B i ⊆ H` and reals `β i`, this is
  the function on `Γ \ H` given by `x ↦ (∑'ᵢ 1_{image of B i}(x) · ofReal (β i)).toReal`. The sum
  is taken in `ℝ≥0∞`, so the positive parts `max (β i) 0` are summed.
- `tsum_ofReal_ne_top`: for a summable real family `β`, `∑' i, ENNReal.ofReal (β i) ≠ ∞`, since
  it is bounded by `ofReal (∑' i, |β i|)`.
- `le_imageIndicatorSum`: if `β` is summable and `x` lies in the image of `B i`, then
  `β i ≤ imageIndicatorSum Γ B β x`. The extended sum is finite by `tsum_ofReal_ne_top`, and it
  dominates its `i`-th term.
- `integrable_imageIndicatorSum`: let `Γ` be discrete, `ν` a `Γ`-invariant measure, `ι`
  countable, `B i` compact with `ν (B i) ≤ m < ∞`, and `β` summable. Then
  `imageIndicatorSum Γ B β` is integrable for `discreteQuotientMeasure Γ hΓ ν`. Its lower
  integral is `∑ᵢ ofReal (β i) · μ(image of B i) ≤ m · ∑ᵢ ofReal (β i) < ∞`, by
  `lintegral_tsum` and `quotientMeasure_mk_image_le` with the Library's fundamental domain.
- `mk_out`: `mk Γ (Quotient.out x) = x`.

## `exists_integrable_majorant_of_cover`

Setting:

- `ν` is a left-invariant measure on `H`, and `Ω ⊆ H` is compact with `ν Ω < ∞`.
- `Γ` is a subgroup of `H`, and `Γw` is a discrete subgroup of `H`.
- `cls : Γ → E` maps to a countable type `E`, with `cls δ = cls δ'` implying `δ' δ⁻¹ ∈ Γw`. In
  other words, each fibre of `cls` lies in a single right coset `Γw δ`.
- `β : E → ℝ` is summable.

Conclusion: there is a function `b` on `Γw \ H`, integrable for `discreteQuotientMeasure Γw hΓw ν`,
with `β (cls δ) ≤ b (Γw · δ ω)` for all `δ ∈ Γ` and `ω ∈ Ω`.

Proof: for each class `i` in the image of `cls`, choose a representative `rep i ∈ Γ` and put
`B i = rep i · Ω`. For classes outside the image, put `B i = ∅`. Left invariance gives
`ν (B i) ≤ ν Ω`. Take `b = imageIndicatorSum Γw B β`, which is integrable by the previous item.
For `δ ∈ Γ` and `ω ∈ Ω`, the hypothesis on `cls` gives `δ · rep(cls δ)⁻¹ ∈ Γw`. Hence
`Γw δ ω = Γw rep(cls δ) ω` lies in the image of `B (cls δ)`, and `le_imageIndicatorSum` applies.
