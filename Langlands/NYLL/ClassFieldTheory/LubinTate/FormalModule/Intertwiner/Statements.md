# NYLL M348.002, M348.003, M348.006 and M348.007: elementary intertwining targets

This module states, as Prop-valued targets, exactly the four theorems of the
source module `Nyll.ClassFieldTheory.LubinTate.FormalModule.Intertwiner`: the
inserted series `e(X_i)` has zero constant coefficient, the inserted family
admits multivariable substitution when the variable type is finite, the
intertwining equation is equivalent to vanishing of its defect, and each
variable `X_i` intertwines a Lubin–Tate series with itself. Nothing is proved
here; each target is to be proved later as a theorem of the same name without
the `Statement` suffix.

## Original source

Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/Intertwiner.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/Intertwiner.lean`.
The source-file SHA-256 is
`334516024f5516e2303b6db285978e437b43bcfce8e38939c6536b7c46079afb`.
The readable original is at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/Intertwiner.lean`.
The registered sources are `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and the
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable NYLL entry was found in `notes/errata/`.

## Source correspondence

All names below are in the namespace `LubinTate.SameUniformizer` (source) and
`Langlands.NYLL.LubinTate.SameUniformizer` (adapted).

| Source unit | Original theorem and lines | Adapted target (Lean lines) |
| --- | --- | --- |
| M348.002 | `constantCoeff_inVariable`, 38–44, `@[simp]` | `constantCoeff_inVariableStatement` (44–46) |
| M348.003 | `inVariable_hasSubst`, 46–51 | `inVariable_hasSubstStatement` (50–52) |
| M348.006 | `intertwines_iff_defect_eq_zero`, 68–73 | `intertwines_iff_defect_eq_zeroStatement` (56–59) |
| M348.007 | `intertwines_X`, 75–81 | `intertwines_XStatement` (63–65) |

The section context of source lines 22–31 is retained: universes `u v`,
`open LocalFieldTheory.DiscreteValuationField`, and the section variables

```lean
variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type*}
```

As in the published definition module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions`,
`LocalField` resolves to the shared published
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K`,
`LubinTateSeries F π` to the published `Langlands.NYLL.LubinTate.LubinTateSeries F π`,
and `inVariable`, `Intertwines` and `defect` to the published M348.001,
M348.004 and M348.005 definitions of that module.

Each target has the complete parameter list of its source theorem, in source
order. A private `#check` probe shows the telescopes

- `constantCoeff_inVariableStatement : {K : Type u} → [Field K] → {F : LocalField K} → {π : F.valuationSubring} → {σ : Type _} → LubinTateSeries F π → σ → Prop`;
- `inVariable_hasSubstStatement : {K} → [Field K] → {F} → {π} → {σ} → [Finite σ] → LubinTateSeries F π → Prop`;
- `intertwines_iff_defect_eq_zeroStatement : {K} → [Field K] → {F} → {π} → {σ} → LubinTateSeries F π → LubinTateSeries F π → MvPowerSeries σ F.valuationSubring → Prop`;
- `intertwines_XStatement : {K} → [Field K] → {F} → {π} → {σ} → [Finite σ] → LubinTateSeries F π → σ → Prop`,

matching the source theorems' binders `{K} [Field K] {F} {π} {σ}`, the source
`[Finite σ]` hypotheses of M348.003 and M348.007, and their explicit
arguments. The universes of `K`, of the value group of `F`, and of `σ` are
independent. The element `π` is arbitrary in `F.valuationSubring`; no
uniformizer hypothesis is added, and no `Finite σ` hypothesis is added to
M348.002 or M348.006.

## Mathematical meaning

Write `O = F.valuationSubring`, let `e, ebar : LubinTateSeries F π` (series in
`O⟦X⟧` with zero constant coefficient and linear coefficient `π`), `i : σ`,
and `H : MvPowerSeries σ O`. Recall `inVariable e i` is
`PowerSeries.subst (MvPowerSeries.X i) e.toPowerSeries`, the series `e(X_i)`.

- **M348.002**, `constantCoeff_inVariableStatement e i`:
  `MvPowerSeries.constantCoeff (inVariable e i) = 0`. The series `e(X_i)` has
  zero constant coefficient.
- **M348.003**, `inVariable_hasSubstStatement e` (with `[Finite σ]`):
  `MvPowerSeries.HasSubst (fun i : σ ↦ inVariable e i)`. In Mathlib this means
  every `e(X_i)` has nilpotent constant coefficient and, for each exponent
  `d`, only finitely many `i` have a nonzero `d`-th coefficient; thus the
  family `i ↦ e(X_i)` can be substituted into multivariable series over `σ`
  and the algebraic laws of `MvPowerSeries.subst` apply to it.
- **M348.006**, `intertwines_iff_defect_eq_zeroStatement e ebar H`:
  `Intertwines e ebar H ↔ defect e ebar H = 0`. The literal intertwining
  equation `e(H) = H(ebar(X_i))_i` holds exactly when the difference of its
  two sides vanishes. No `HasSubst` or finiteness hypothesis appears, as in
  the source.
- **M348.007**, `intertwines_XStatement e i` (with `[Finite σ]`):
  `Intertwines e e (MvPowerSeries.X i)`, i.e. `e(X_i) = X_i(e(X_j))_j`: the
  coordinate series `X_i` intertwines `e` with itself.

## Using the later proofs

The targets are `abbrev`s, so a theorem
`theorem constantCoeff_inVariable … : constantCoeff_inVariableStatement e i`
can carry the source `@[simp]` attribute, and `simp`, `simp only [...]`,
`.mp`/`.mpr` and direct term use see the underlying proposition. A private
probe confirmed that `simp` closes `MvPowerSeries.constantCoeff (inVariable e i) = 0`
with a `@[simp]` proof of M348.002, that `simp only [intertwines_iff_defect_eq_zero]`
rewrites with a proof of M348.006, and that a proof of M348.003 can be passed to
`MvPowerSeries.subst_add` and `MvPowerSeries.subst_X`. Two usage points differ
from the source theorems:

- `rw [intertwines_iff_defect_eq_zero]` does not rewrite, because `rw` does not
  unfold the target to its `↔`; use `simp only`, `.mp`/`.mpr`, or ascribe the
  proposition with `show` first.
- The explicit arguments of `inVariable_hasSubstStatement e` do not mention
  `σ`, so a proof that states it must name the variable type, e.g.
  `inVariable_hasSubstStatement (σ := σ) e`. Uses of the proof at an expected
  `MvPowerSeries.HasSubst (fun i : σ ↦ inVariable e i)` infer `σ` as before.

## Dependencies and modification record

The only import is the sibling published definition module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions`,
which provides `inVariable`, `Intertwines` and `defect` and, through its own
imports, `LubinTateSeries`, `LocalField`, `MvPowerSeries.HasSubst`,
`MvPowerSeries.subst` and `PowerSeries.subst`.

The complete adaptations are:

1. each of the four source theorems is replaced by a Prop-valued `abbrev`
   named `<source name>Statement`, whose binders are the source theorem's
   binders and whose body is the source theorem's conclusion verbatim; the
   source proofs are omitted, and the `@[simp]` attribute of M348.002 is left
   to its later proof;
2. the `Langlands.NYLL` prefix on the namespaces `LubinTate` and
   `SameUniformizer`;
3. the source definitions are not repeated; they are imported from the
   published definition module;
4. the source `noncomputable section` is omitted, since the module declares
   only propositions;
5. a modified-file notice in the header, a new module docstring and new
   declaration docstrings naming the targeted source units.

The original 2026 copyright, Apache-2.0 release line and author header are
preserved. Existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are
unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`; the
NOTICE has no entry specific to this source file, and the supplement's
`files/Nyll/ClassFieldTheory/ANTHROPIC_FLT_SOURCE.md` list of
Anthropic-derived files does not include it.
