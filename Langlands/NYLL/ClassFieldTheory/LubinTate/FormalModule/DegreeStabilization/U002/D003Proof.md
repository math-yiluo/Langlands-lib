# NYLL M351.003: truncation of `H(ebar(X_i))_i` depends only on the truncation of `H` (proof)

This module proves the published target
`Langlands.NYLL.PortInternal.M351.d003Statement` as the theorem
`Langlands.NYLL.PortInternal.M351.d003` (adapted name of the source-private
theorem `LubinTate.SameUniformizer.truncTotal_inVariables_subst_eq_of_truncTotal_eq`).
For `ebar : LubinTateSeries F π`, `H H' : MvPowerSeries σ F.valuationSubring`
over a `Finite` type `σ` and `htrunc : H.truncTotal k = H'.truncTotal k`,
it proves
`(MvPowerSeries.subst (fun i ↦ inVariable ebar i) H).truncTotal k = (MvPowerSeries.subst (fun i ↦ inVariable ebar i) H').truncTotal k`.
The theorem has the binders of the target (section variables
`{K} [Field K] {F : LocalField.{u,v} K} {π} {σ : Type w}`, then
`[Finite σ] (ebar) {H H'} {k} (htrunc)`) and its type is
`d003Statement ebar htrunc`.

## Original source

Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`
(SHA-256 `2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`),
readable at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`;
registered sources `external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`.

The proof follows source lines 116–133 (statement 109–115), with one change
in the first step, described below.

## Proof

First, every `inVariable ebar i = PowerSeries.subst (X i) ebar.toPowerSeries`
has zero constant coefficient. The source cites `constantCoeff_inVariable`
(M348.002); this proof instead applies Mathlib's
`PowerSeries.constantCoeff_subst_eq_zero` to
`MvPowerSeries.constantCoeff_X i` and `ebar.constantCoeff_eq_zero` (the
zero constant coefficient field of `LubinTateSeries`), so the M348.002
proof is not needed. A three-step `calc` then applies Mathlib's
`MvPowerSeries.truncTotal_subst_eq_truncTotal_truncTotal_subst` (with this
constant-coefficient fact) to replace `H` by `(H.truncTotal k).toMvPowerSeries`
inside the truncated substitution, rewrites with `htrunc`, and applies the
same lemma backwards for `H'`.

## Imports and adaptations

Imports: the published statement module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.U002.Statements`
(which provides `inVariable` through the published M348 definitions) and
`Mathlib.RingTheory.MvPowerSeries.Substitution`. Adaptations: the
source-private theorem is renamed `Langlands.NYLL.PortInternal.M351.d003` and
placed in that namespace with the source section context restated and the
opens written with full names; its type is written as the target; the
constant-coefficient step is computed from Mathlib as described; the section
instance `[Fintype σ]`, omitted by the source for this theorem, is not
declared; `noncomputable section` and `open scoped BigOperators` are
omitted; a modified-file notice and docstrings are added.
The original 2026 copyright, Apache-2.0 release line and author header are
preserved; `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are unchanged.
