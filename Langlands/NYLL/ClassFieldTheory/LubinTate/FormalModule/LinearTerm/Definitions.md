# NYLL M347.001 and M347.003: prescribed linear terms

These two definitions are adapted from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LubinTate/FormalModule/LinearTerm.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/LinearTerm.lean).
The readable original is at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/LinearTerm.lean`.
Its file SHA-256 is
`154a6f23a3514dce4d5b450d51a65db7d3038029c43a56b58f95faecb7d3872d`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The associated attribution and verification supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL entry was found in `notes/errata/`.

## Source correspondence and meaning

| Source unit | Original declaration and lines | Adapted declaration |
| --- | --- | --- |
| M347.001 | `LubinTate.SameUniformizer.linearForm`, 28–29 | `Langlands.NYLL.LubinTate.SameUniformizer.linearForm` |
| M347.003 | `LubinTate.SameUniformizer.HasLinearTerm`, 39–40 | `Langlands.NYLL.LubinTate.SameUniformizer.HasLinearTerm` |

For a commutative ring `R`, a finite variable type `σ`, and coefficients
`L : σ → R`, `linearForm L` is the finite sum
`∑ i, MvPowerSeries.C (L i) * MvPowerSeries.X i`.
It is a noncomputable definition with values in `MvPowerSeries σ R`.
The predicate `HasLinearTerm H L` is exactly
`(2 : ℕ∞) ≤ (H - linearForm L).order`, using Mathlib's total order of a
multivariable power series.

The source section parameters at lines 24–25 are retained:
`{R : Type*} [CommRing R] {σ : Type*} [Fintype σ]`.
The coefficient and variable universes remain independent. The coefficient
function `L` is explicit; the predicate also takes an explicit series `H`.
There are no field, local-field, nonempty-variable, or characteristic hypotheses.

## Modifications and reuse

Worker 342 extracted these two definitions on 13 November 2026. Their bodies,
docstrings, binder kinds, and the source's `noncomputable section` and explicit
`noncomputable def linearForm` are retained. The namespace is prefixed with
`Langlands.NYLL` and written as one namespace command. The source's
`Mathlib.RingTheory.PowerSeries.Substitution` import is omitted because these
definitions use only `Mathlib.RingTheory.MvPowerSeries.Order`. Source theorem
declarations M347.002, M347.004, and M347.005 are omitted. The module description
is retained, whitespace is normalized, and a modification notice is added.
No feasibility-patch edits are used.

Mathlib's `MvPowerSeries`, constant series `C`, variables `X`, and `order`
are reused directly. Searches of the current Library and Mathlib's power-series
modules found no existing equivalent pair of definitions. This unit introduces
no theorem targets or proofs; the constant-coefficient and substitution
consequences belong to separate work.

The original 2026 copyright, Apache-2.0 release, and authorship header are
retained verbatim. The existing `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
are preserved unchanged.
