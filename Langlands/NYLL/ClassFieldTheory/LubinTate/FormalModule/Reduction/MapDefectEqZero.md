# NYLL M349.005: the reduced intertwining defect vanishes

This module proves the published proposition
`Langlands.NYLL.LubinTate.SameUniformizer.map_defect_eq_zeroStatement` by the
theorem `Langlands.NYLL.LubinTate.SameUniformizer.map_defect_eq_zero`.
It imports four published modules, none of which is changed:

- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.Statements`
  (the target);
- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.ExpandNatCard`
  (M349.001, `mvPowerSeries_expand_natCard`);
- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.MapSubstLubinTateSeries`
  (M349.003, `map_subst_lubinTateSeries`);
- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.MapSubstInVariables`
  (M349.004, `map_subst_inVariables`).

## Target and mathematical meaning

The theorem lives in namespace `Langlands.NYLL.LubinTate.SameUniformizer`
and has the target's exact telescope: implicit `K : Type u` with
`[Field K]`, implicit `F : LocalField.{u, v} K`, implicit
`π : F.valuationSubring`, implicit `σ : Type w` with `[Fintype σ]`, the
explicit `e ebar : LubinTateSeries F π`, implicit
`H : MvPowerSeries σ F.valuationSubring` and `L : σ → F.valuationSubring`,
and the explicit hypothesis `hH : HasLinearTerm H L`. Its type is
`map_defect_eq_zeroStatement e ebar hH`, which unfolds to

```lean
MvPowerSeries.map F.residueMap (defect e ebar H) = 0
```

Here the published `defect e ebar H` is
`PowerSeries.subst H e.toPowerSeries -
MvPowerSeries.subst (fun i ↦ inVariable ebar i) H`, the difference of the two
sides `e(H)` and `H(ebar(X_1), …)` of the same-uniformizer intertwining
equation. Mathematically: with `q = Nat.card F.residueField`, the left side
reduces to `Hbar ^ q` (M349.003, using that `H` has a prescribed linear term),
the right side reduces to `Hbar(X_1 ^ q, …)` (M349.004), and over the finite
residue field `Hbar(X_1 ^ q, …) = Hbar ^ q` (M349.001). So the reduced
defect is zero. No uniformizer hypothesis is used; the two series share only
the arbitrary linear coefficient `π`.

## Implemented proof

1. `show _ = _` unfolds the reducible target to the displayed equation.
2. One `rw` chain rewrites
   - `defect` (unfolding the published definition into the difference),
   - `map_sub` (reduction is additive),
   - `map_subst_lubinTateSeries e hH` (left term becomes `Hbar ^ q`),
   - `map_subst_inVariables ebar H` (right term becomes the expansion of
     `Hbar`; `[Finite σ]` is inferred from `[Fintype σ]`),
   - `mvPowerSeries_expand_natCard` (the expansion becomes `Hbar ^ q`; the
     residue field is finite by its `LocalField` structure),

   leaving `Hbar ^ q - Hbar ^ q = 0`.
3. `exact sub_self _` closes it.

The three theorems used by `rw` have reducible `abbrev` targets, so `rw`
sees their equations directly. Dependencies: the published definition
`defect`, the published theorems listed above, and Mathlib's `map_sub` and
`sub_self`. No auxiliary declaration, instance or simp attribute is added.

## Source and attribution

This is M349.005, theorem `LubinTate.SameUniformizer.map_defect_eq_zero`,
lines 110–119 of Naganori Yamaguchi's
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
lists this unit as M349.005. No patch10 edit applies, and no applicable NYLL
erratum was found in the published errata notes.

The implemented proof is the source proof (lines 116–119), the same `rw`
chain and `exact sub_self _`, preceded only by `show _ = _`. The source's
references to M349.001, M349.003 and M349.004 resolve to the published
theorems of the same names.

## Modification record

- Extract only M349.005 into this focused module; prefix the namespace with
  `Langlands.NYLL`.
- Import the published Reduction statement module and the published
  M349.001, M349.003 and M349.004 proof modules instead of the source imports.
- State the conclusion as the published target
  `map_defect_eq_zeroStatement e ebar hH` and unfold it with a leading
  `show _ = _`.
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
