# Haar measures on discrete left quotients

For a subgroup `Γ` of a group `H`, this module proves nonvanishing and local
finiteness of the explicit measure on the left quotient `Γ \ H`. It then
constructs `haarQuotientMeasure` from Mathlib's actual ambient `Measure.haar`.
The carrier and positive right translations are those of `LeftCosetSpace`.
No subgroup normality is required.

`preimage_image_mk` identifies the saturation of a set `A` with the union
`⋃ γ : Γ, γ • A`. This algebraic identity has no topological, measurable or
countability hypothesis. For a countable subgroup whose constant left
actions are measurable, `measurableSet_image_mk` shows that the quotient image
of a measurable set is measurable for the inherited quotient sigma algebra.

Let `ν` be invariant under the left `Γ` action and let `s` be a fundamental
domain for that action and measure. Under the preceding countability and
action-measurability hypotheses, `quotientMeasure_image_le` proves
`quotientMeasure Γ ν s (mk Γ '' A) ≤ ν A` for measurable `A`.
The saturation identity and countable subadditivity bound the left side by
`∑' γ : Γ, ν (γ • A ∩ s)`, which equals `ν A` by the
fundamental-domain decomposition.

`quotientMeasure_ne_zero` requires a countable `Γ`, its invariant measure
and a fundamental domain, and assumes `ν ≠ 0`. A fundamental domain then has
nonzero measure. Since the total mass of its restricted pushforward is
`ν s`, the quotient measure is nonzero. This argument does not require
measurable constant actions.

If `H` is a topological group with its Borel measurable structure and `ν`
is locally finite, `isLocallyFiniteMeasure_quotientMeasure` proves local
finiteness of the quotient measure at the same countable invariant-action
and fundamental-domain hypotheses. Choose an open neighborhood of a
representative with finite ambient measure. The quotient projection is
open, and the image bound makes its image a finite-measure neighborhood.
Neither local compactness nor separation is required for this argument.

For a discrete subgroup of a second-countable Borel topological group,
`discreteQuotientMeasure_ne_zero` and
`isLocallyFiniteMeasure_discreteQuotientMeasure` apply these results to
the chosen Borel domain of `LeftCosetFundamentalDomain`. Here countability
and domain existence are derived. These two conclusions require a
left-invariant ambient measure, together with nonzero or local finiteness,
respectively.

`regular_discreteQuotientMeasure` assumes in addition that `H` is locally
compact and Polish and that the ambient left-invariant measure is locally
finite. Polishness supplies second countability and Hausdorffness. A
discrete subgroup is closed, so its quotient is Hausdorff; the open
projection also supplies local compactness and second countability.
`quotient_borelSpace` identifies the inherited quotient sigma algebra
with the Borel sigma algebra. The quotient is metrizable and sigma compact,
so Mathlib's
`Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure`
gives regularity of its locally finite measure.

For a locally compact, second-countable Borel topological group and a
discrete subgroup, `haarQuotientMeasure Γ hΓ` is exactly
`discreteQuotientMeasure Γ hΓ (Measure.haar : Measure H)`.
Its nonzero and local-finiteness theorems use the corresponding ambient
Haar properties. `regular_haarQuotientMeasure` assumes the locally compact
Borel topological group is Polish; it uses the regularity result above.
`measurePreserving_rightTranslate_haarQuotientMeasure` assumes explicitly
that this ambient Haar measure is also right invariant and proves
invariance under every positive right translation `[x] ↦ [x*g]`.

Provenance is internal. The saturation and fundamental-domain decomposition
are pinned Mathlib group-action and measure results, the image bound is
countable subadditivity, and local finiteness uses the open quotient map.
Regularity follows from the checked Borel, metrizability and sigma-compactness
hypotheses of Mathlib's regularity theorem. The Haar normalization is the
actual choice made by `Measure.haar`.

This module does not identify the measure with the separate
`Langlands.QuotientIntegration.IsCompatible` construction or its Weil
formula. Actual adelic point topology, rational discreteness, reductive
unimodularity, the analytic Haar-modulus comparison, finite covolume,
probability normalization, reduction theory and the split-centre comparison
remain separate obligations.
