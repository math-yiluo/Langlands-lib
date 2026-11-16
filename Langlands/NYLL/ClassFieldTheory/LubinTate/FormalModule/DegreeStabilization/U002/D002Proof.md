# NYLL M351.002: truncation of `e(H)` depends only on the truncation of `H` (proof)

This module proves the published target
`Langlands.NYLL.PortInternal.M351.d002Statement` as the theorem
`Langlands.NYLL.PortInternal.M351.d002` (adapted name of the source-private
theorem `LubinTate.SameUniformizer.truncTotal_powerSeries_subst_eq_of_truncTotal_eq`).
For `e : LubinTateSeries F π`, `H H' : MvPowerSeries σ F.valuationSubring`
over a `Finite` type `σ` with `hH : constantCoeff H = 0`,
`hH' : constantCoeff H' = 0` and `htrunc : H.truncTotal k = H'.truncTotal k`,
it proves
`(PowerSeries.subst H e.toPowerSeries).truncTotal k = (PowerSeries.subst H' e.toPowerSeries).truncTotal k`.
The theorem has the binders of the target (section variables
`{K} [Field K] {F : LocalField.{u,v} K} {π} {σ : Type w}`, then
`[Finite σ] (e) {H H'} (hH) (hH') {k} (htrunc)`) and its type is
`d002Statement e hH hH' htrunc`.

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

The proof is that of source lines 81–107 (statement 72–80), unchanged.

## Proof

Zero constant coefficient gives `PowerSeries.HasSubst H` and
`PowerSeries.HasSubst H'` (`PowerSeries.HasSubst.of_constantCoeff_zero`).
`change` rewrites the one-variable substitutions as multivariable
substitutions `MvPowerSeries.subst (fun _ : Unit ↦ H) e.toPowerSeries`
(definitional unfolding of `PowerSeries.subst`). A three-step `calc` then
applies Mathlib's
`MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le`
(with `x := fun _ ↦ k`, the `HasSubst` fact via `.const`, and `le_rfl`)
to replace `H` by `(H.truncTotal k).toMvPowerSeries` inside the
truncation, rewrites with `htrunc`, and applies the same lemma backwards for
`H'`.

## Imports and adaptations

Imports: the published statement module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.U002.Statements`
and `Mathlib.RingTheory.MvPowerSeries.Substitution` (the truncation and
substitution lemma). Adaptations: the source-private theorem is renamed
`Langlands.NYLL.PortInternal.M351.d002` and placed in that namespace with the
source section context restated and the opens written with full names
(`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`,
`Langlands.NYLL.LubinTate`, `Langlands.NYLL.LubinTate.SameUniformizer`);
its type is written as the target; the section instance `[Fintype σ]`,
omitted by the source for this theorem, is not declared; the source's
`noncomputable section` and `open scoped BigOperators` are omitted; a
modified-file notice and docstrings are added.
The original 2026 copyright, Apache-2.0 release line and author header are
preserved; `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are unchanged.
