# NYLL M349.002: reduction of an inserted Lubin--Tate series

This module proves the published proposition
`Langlands.NYLL.LubinTate.SameUniformizer.map_inVariableStatement` by the
theorem `Langlands.NYLL.LubinTate.SameUniformizer.map_inVariable`. Its only
import is the published statement module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.Statements`,
which is not changed.

## Target and mathematical meaning

The theorem lives in namespace `Langlands.NYLL.LubinTate.SameUniformizer`
and has the target's exact telescope: implicit `K : Type u` with
`[Field K]`, implicit `F : LocalField.{u, v} K`, implicit
`π : F.valuationSubring`, implicit `σ : Type w` (no finiteness instance, as
in the source's `omit [Fintype σ] in`), and the explicit arguments
`(e : LubinTateSeries F π) (i : σ)`. Its type is
`map_inVariableStatement e i`, which unfolds to

```lean
MvPowerSeries.map F.residueMap (inVariable e i) =
  (MvPowerSeries.X i : MvPowerSeries σ F.residueField) ^
    Nat.card F.residueField
```

Here `inVariable e i = PowerSeries.subst (MvPowerSeries.X i) e.toPowerSeries`
is the one-variable Lubin--Tate series `e` inserted into the variable `X_i`.
Mathematically: since `e` reduces modulo the maximal ideal to the Frobenius
series `X ^ q` with `q = Nat.card F.residueField` (the structure field
`LubinTateSeries.map_residue_eq_frobenius`), the series `e(X_i)` reduces to
`X_i ^ q`. No uniformizer, finiteness or nonemptiness hypothesis is used.

## Implemented proof

1. `show _ = _` unfolds the reducible target to the displayed equation.
2. `hX` and `hXbar` record Mathlib's `PowerSeries.HasSubst.X i` over the
   valuation subring and over the residue field.
3. One `rw` chain then rewrites
   - `inVariable` (unfolding the published definition),
   - `PowerSeries.map_subst hX e.toPowerSeries` (reduction commutes with
     substitution of `X_i`),
   - `e.map_residue_eq_frobenius` (the reduced series is `X ^ q`),
   - `MvPowerSeries.map_X` (the reduced variable is `X_i`),
   - `PowerSeries.subst_pow hXbar` and `PowerSeries.subst_X hXbar`
     (substituting `X_i` into `X ^ q` gives `X_i ^ q`),

   after which the two sides agree syntactically and `rw` closes the goal.

Dependencies: the published definitions `inVariable` and `LubinTateSeries`
(through the statement module) and the Mathlib lemmas named above. No
auxiliary declaration, instance or simp attribute is added.

## Source and attribution

This is M349.002, theorem `LubinTate.SameUniformizer.map_inVariable`, lines
61–75 of Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FormalModule/Reduction.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/Reduction.lean)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The source-file SHA-256
is `b9a7d469a06616be19f5841ca96c26f22887650ccf4d83336a84ab89b2ccb2ad`
(recomputed by Worker 465 on 15 November 2026). The retained original is
under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registrations are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The [port partition](../../../../../../notes/reuse/nyll-public-port/m337-m360.md#m349)
lists this unit as M349.002. No patch10 edit applies, and no applicable NYLL
erratum was found in the published errata notes.

The implemented proof is the source proof: the same two `HasSubst` facts and
the same `rw` chain, preceded only by `show _ = _`.

## Modification record

- Extract only M349.002 into this focused module; prefix the namespace with
  `Langlands.NYLL`.
- Import the published Reduction statement module instead of the source
  imports.
- State the conclusion as the published target `map_inVariableStatement e i`
  and unfold it with a leading `show _ = _`.
- Declare `σ` without `[Fintype σ]` directly instead of the source's section
  variable plus `omit [Fintype σ] in`; the resulting binders are the same.
- Append the unit label to the source docstring, and replace the module
  documentation.

The Lean file keeps the original 2026 Naganori Yamaguchi copyright, Apache-2.0
and author header verbatim, followed by Worker 465's dated modification
record. The unchanged inherited
[LICENSE](../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are already
in the Library. No published statement or definition is edited.

## Environment

Development environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`): the module compiles with
no errors or warnings. Compilation is not acceptance; publication requires the
Lake build, exact-target and unchanged-statement checks, independent semantic
review and integration.
