# Recursive monomial corrections: data definitions

This module defines the two data declarations M352.001 and M352.002 of the
recursive same-uniformizer intertwiner construction. It proves nothing.

## Source and attribution

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveCorrection.lean`.
Its SHA-256 is
`87e0549f80ad2537095f3e36ee939774ac0f09d041e36463f6f84e7df1a71edb`.
It is readable in registered source
`external-lean-reuse-snapshots-2026-10-21` under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
registered as `nyll-classfieldtheory-fbd320cd-supplement`.

The original copyright, Apache-2.0 and author header is preserved in the Lean
file. The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply.
Worker 496 made the adaptations listed below. No patch10 edit affects this
source module.

## Definitions

Both definitions are in `Langlands.NYLL.LubinTate.SameUniformizer`. They keep
the source section variables (lines 31–33): `{K : Type u} [Field K]`,
`{F : LocalField.{u, v} K}`, `{π : F.valuationSubring}` and
`{σ : Type w} [Fintype σ]`, with the three independent universes `u v w`
(line 24). `LocalField` is the published adapted
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField`, which
extends the published `CompleteDVF`; `LubinTateSeries F π` is the published
`Langlands.NYLL.LubinTate.LubinTateSeries`.

Each definition takes, in source order: an explicit proof
`hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)`, explicit
`e ebar : LubinTateSeries F π`, implicit
`H : MvPowerSeries σ F.valuationSubring` and `L : σ → F.valuationSubring`,
an explicit proof `hH : HasLinearTerm H L`, an explicit multidegree
`d : σ →₀ ℕ` and an explicit proof `hd : 2 ≤ d.degree`. Both return
`MvPowerSeries σ F.valuationSubring`.

| Source unit and lines | Declaration | Body |
| --- | --- | --- |
| M352.001, lines 35–44 | `monomialCorrection hπ e ebar hH d hd` | `MvPowerSeries.monomial d (correctionCoefficient hπ e ebar hH d hd)` |
| M352.002, lines 46–54 | `correctedIntertwiner hπ e ebar hH d hd` | `H + monomialCorrection hπ e ebar hH d hd` |

Mathematically, `monomialCorrection` is the single monomial
`c_d X^d`, where `c_d = correctionCoefficient hπ e ebar hH d hd` is the
scalar selected in M350.003 (Task 6080) by `Classical.choose` from the
unique solvability of `(1 - π ^ (d.degree - 1)) * c = -n_d` in the valuation
ring, where `n_d` is the normalized degree-`d` defect coefficient of `H`
(`π * n_d` is the `d` coefficient of `defect e ebar H`). `correctedIntertwiner` is the next
approximation `H + c_d X^d`. Both bodies are definitional and use no theorem;
the choice is entirely inside the imported `correctionCoefficient`.

The predicate `HasLinearTerm H L` is the published
`(2 : ℕ∞) ≤ (H - linearForm L).order`; it enters only as an argument passed
to `correctionCoefficient`.

## Imports and omitted source units

The source imports the whole `RecursiveCoefficient` and
`DegreeStabilization` modules (lines 7–8). This module imports only the
published focused module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient.CorrectionCoefficient`
containing `correctionCoefficient`, which transitively supplies
`LocalField`, `LubinTateSeries`, `HasLinearTerm` and Mathlib's multivariable
power series. No declaration of `DegreeStabilization` (M351) is used by the two
bodies. The source `correctionCoefficient_unique` (M350.005) is not used by
either body and is not imported; this module compiled successfully without
any name or import providing it (see the verification section).

## Adaptations

The following are all modifications to the selected source declarations and
their surrounding interface:

- Split the two definitions from the original module, which also contains
  the theorems M352.003 and M352.004 (published separately as Prop targets
  followed by exact proofs).
- Prefix the namespace `LubinTate.SameUniformizer` with `Langlands.NYLL`;
  the source's `open LocalFieldTheory.DiscreteValuationField` therefore
  resolves to the adapted `Langlands.NYLL` namespace.
- Replace the two source imports by the focused published import above.
- Remove the unused `open scoped BigOperators`.
- Replace the module documentation; the two declaration docstrings are
  unchanged.

The declaration names, parameter names, binder kinds, parameter order,
universes, types and bodies are unchanged.

## Development verification

Compiled in approved environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) over
Library commit `ccd5c6bb63352c109b2bfde422a65c2dd78e57fd`, which contains
the published `correctionCoefficient`, with no warnings or errors
(private diagnostic `fac5baf0-5691-438d-800f-1e1a7e467174`). Development
compilation is not independent acceptance.
