# NYLL M354.013: proof of the zero intertwiner

`Langlands.NYLL.LubinTate.SameUniformizer.intertwines_zero` proves the exact
published target `intertwines_zeroStatement (σ := σ) e ebar`.
For `[Finite σ]` and two Lubin–Tate series with the same field package and
prescribed coefficient, the zero multivariable series satisfies their
intertwining equation.

## Source and exact scope

The source is Naganori Yamaguchi,
[`Nyll/ClassFieldTheory/LubinTate/FormalModule/StandardFormalGroup.lean`,
lines 309–325](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/StandardFormalGroup.lean#L309-L325),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, original declaration
`LubinTate.SameUniformizer.intertwines_zero`. The original file's SHA-256 is
`c563068d157ec2664f0e81603050248add1d49e955b55b5a380a5322d4f3415d`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered sources are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable NYLL erratum was found in the current published errata notes.

The complete telescope, in source order, is
`{K : Type u} [Field K] {F : LocalField.{u,v} K}
{π : F.valuationSubring} {σ : Type w} [Finite σ]
(e ebar : LubinTateSeries F π)`, with independent universes `u`, `v`, `w`.
The conclusion is exactly `intertwines_zeroStatement (σ := σ) e ebar`.
The unused source section variable `τ` and its universe do not enter the
declaration. There is no additional `HasSubst` hypothesis and no replacement
of `Finite` by `Fintype`. The coefficient `π` is arbitrary; no uniformizer
assumption is introduced. The proof uses the published shared `LocalField`
extending `CompleteDVF`, `LubinTateSeries`, `Intertwines` and `inVariable`.

## Implemented proof

First expose the published proposition's literal `Intertwines` conclusion.
The remaining proof follows source lines 316–325. Unfold `Intertwines` and
express the left side as multivariable substitution into `e.toPowerSeries`
by the zero `Unit`-indexed family. Apply
`MvPowerSeries.subst_zero_of_constantCoeff_zero` with
`e.constantCoeff_eq_zero` to make that side zero. For the right side, the
published M348.003 theorem `inVariable_hasSubst ebar` supplies substitution
for the family `i ↦ inVariable ebar i`. Rewrite with
`MvPowerSeries.substAlgHom_apply` and finish with `map_zero`.
The required substitution premise is thus proved from the Lubin–Tate
structure and `[Finite σ]`, rather than added to the theorem's hypotheses.

## Imports and dependency boundary

The only direct imports are:

- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.SubstitutionClosure.U013.Statements`;
- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.InVariableHasSubst`.

The first supplies the exact published target and literal definitions. The
second supplies the independently published M348.003 proof. Its private
constant-coefficient helper uses
`PowerSeries.constantCoeff_subst_eq_zero`,
`MvPowerSeries.constantCoeff_X` and `e.constantCoeff_eq_zero`.
The zero-substitution and algebra-homomorphism laws used here are provided
by the existing Mathlib substitution modules.

Neither M353 (`RecursiveIntertwiner`) nor M354.011 (`Intertwines.reindex`) is used
in this proof route. The source's broad `RecursiveIntertwiner`,
`StandardSeries` and formal-group imports are replaced by the focused
imports above.

A focused `lean_check` of both direct imports and this proof succeeded
with zero errors and warnings in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), diagnostic
`dc28ce18-c2da-4ead-a3de-8b3c0128dd5a`. A separate private Lean import audit,
diagnostic `4be29bbc-eb8f-4f49-b5af-0f0e91700661`, imported only this proof
and also passed with zero errors and warnings. It checked the actual
transitive imported-module list, confirming absence of M353 and the
M354.011 module subtree, absence of `Intertwines.reindex` and its target,
and presence of `inVariable_hasSubst`. The complete imported NYLL list
consists of the shared valued-field and local-field definitions/projections,
`Series.Definitions`, `Intertwiner.Definitions`, `Intertwiner.Statements`,
`Intertwiner.InVariableHasSubst`, and this unit's `Statements` and `Proofs`.
The audit also printed the full telescope and exact target, confirming the
three independent universes and source binder order. These are development
checks; independent review and publication are separate.

## Complete modification and attribution record

Extract only M354.013; add the `Langlands.NYLL` namespace prefix; express
the theorem type through the published target with explicit `σ`; and add
the initial `change` exposing that target. The subsequent source proof is
retained. Replace the original broad imports by the two focused published
imports above. Omit unrelated declarations, the unused `τ`/`w'` section
variables, and unused noncomputability, classical-instance and scope
settings. Adapt the module/declaration documentation and add the
modified-file notice. The mathematical telescope, binder order,
visibility, names, independent universes and hypotheses are preserved.
No patch10 edit affects this source module; no published definition,
statement or imported file is changed.

The original 2026 copyright, Apache-2.0 release and author header are
preserved. Existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain
unchanged, with SHA-256 respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
