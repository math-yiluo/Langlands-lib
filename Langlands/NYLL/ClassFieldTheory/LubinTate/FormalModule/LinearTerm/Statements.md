# Prescribed linear terms: constant coefficient and substitution targets

This module states the signatures of the three theorems M347.002, M347.004
and M347.005. It contains proposition definitions; it does not prove them.

## Source and attribution

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/LinearTerm.lean`.
Its SHA-256 is
`154a6f23a3514dce4d5b450d51a65db7d3038029c43a56b58f95faecb7d3872d`.
It is readable in registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The original copyright, Apache-2.0 and author header is preserved in the Lean
file. The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply.
Worker 343 made the adaptations listed below. No patch10 edit affects this
source module.

## Exact targets and hypotheses

All three targets are in `Langlands.NYLL.LubinTate.SameUniformizer`.
They retain the source's implicit coefficient type `R`, instance `[CommRing R]`,
independent implicit variable type `σ` and instance `[Fintype σ]`
(source lines 24–25). The two universes are independent, represented explicitly
by `R : Type u` and `σ : Type v`.

| Source unit and lines | Target, relative to the namespace above | Proposition |
| --- | --- | --- |
| M347.002, lines 31–35; signature at 33–34 | `constantCoeff_linearFormStatement (L : σ → R)` | `MvPowerSeries.constantCoeff (linearForm L) = 0` |
| M347.004, lines 44–54; signature at 48–49 | `HasLinearTerm.constantCoeff_eq_zeroStatement {H : MvPowerSeries σ R} {L : σ → R} (h : HasLinearTerm H L)` | `MvPowerSeries.constantCoeff H = 0` |
| M347.005, lines 44 and 56–60; signature at 58–59 | `HasLinearTerm.hasSubstStatement {H : MvPowerSeries σ R} {L : σ → R} (h : HasLinearTerm H L)` | `PowerSeries.HasSubst H` |

The last two targets keep the explicit prescribed-linear-term hypothesis.
Its parameter name is `_h` in Lean because a proposition's body does not use
the proof. Their `H` and `L` remain implicit, as in the original.

The imported `linearForm` is the finite sum
`∑ i, MvPowerSeries.C (L i) * MvPowerSeries.X i` (source lines 28–29).
The imported predicate `HasLinearTerm H L` means
`(2 : ℕ∞) ≤ (H - linearForm L).order` (source lines 39–40).
Both belong to the predecessor definition unit, Task 6042; this module reuses
them by Lean name. `PowerSeries.HasSubst H` is Mathlib's predicate for
substitution into a one-variable power series, expressed by nilpotence of
the multivariable series' constant coefficient. No local field, valuation,
nontriviality or nonempty-variable assumption is added.

## Adaptations and proof boundary

The following are all modifications to the selected source declarations and
their surrounding interface:

- Split the three theorem signatures from the original combined module into
  this focused statement module.
- Prefix the original namespaces by `Langlands.NYLL` and append `Statement`
  to the original theorem names.
- Replace each theorem and its proof with a `def` returning `Prop`; preserve
  each signature's parameters and conclusion. Rename the unused hypothesis
  `h` to `_h`.
- Name the two independent universes `u` and `v` explicitly in place of the
  source's two `Type*` binders.
- Import the predecessor's focused `Definitions` module instead of repeating
  the definitions; it supplies the original order interface. Retain the
  source's `Mathlib.RingTheory.PowerSeries.Substitution` import.
- Replace the source module exposition and theorem docstrings with
  statement-specific documentation and this adaptation record. Remove
  the unused `noncomputable section` wrapper.
- Reserve the source's `@[simp]` attribute (line 32) for the eventual theorem
  `Langlands.NYLL.LubinTate.SameUniformizer.constantCoeff_linearForm`;
  no proposition definition receives that theorem attribute.

The source proof routes are finite-sum simplification (M347.002), the order
criterion `MvPowerSeries.one_le_order_iff_constCoeff_eq_zero` after lowering the
order bound from two to one (M347.004), and
`PowerSeries.HasSubst.of_constantCoeff_zero` (M347.005).
These descriptions identify the later proof tasks; this module makes no
proof claim. Each exact theorem is to be routed to a separate `lean.proof@1`
task only after its target has been published.

## Development verification

The focused module was compiled in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) against the published predecessor
definitions. Separate exact-declaration inspections of all three targets
succeeded, reported `statement_returns_prop: true` and independent universe
parameters `u` and `v`, and emitted no warnings or errors.
Development compilation and inspection do not establish independent semantic
acceptance or prove any of the targets.
