# NYLL M354.010: intertwining under multivariable substitution

The theorem
`Langlands.NYLL.LubinTate.SameUniformizer.Intertwines.subst`
proves the published target
`Langlands.NYLL.LubinTate.SameUniformizer.Intertwines.substStatement`.
Its conclusion is the literal equation predicate
`Intertwines e ehat (MvPowerSeries.subst G H)`.

## Source and exact scope

Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`, StandardFormalGroup.lean, lines 230–273](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/StandardFormalGroup.lean#L230),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, supplies the original
declaration `LubinTate.SameUniformizer.Intertwines.subst` and its proof.
The original file SHA-256 is
`c563068d157ec2664f0e81603050248add1d49e955b55b5a380a5322d4f3415d`.
The readable pinned source is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered sources are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

The theorem retains independent universes `u v w w'`, implicit
`{K : Type u} [Field K] {F : LocalField.{u,v} K}`,
implicit `{π : F.valuationSubring} {σ : Type w} {τ : Type w'}`, then
`[Finite σ] [Finite τ]`, implicit `{e ebar ehat : LubinTateSeries F π}`,
implicit `{H : MvPowerSeries σ F.valuationSubring}`, explicit
`(hH : Intertwines e ebar H)`, explicit
`(hHsubst : PowerSeries.HasSubst H)`, implicit
`{G : σ → MvPowerSeries τ F.valuationSubring}`, explicit
`(hGsubst : MvPowerSeries.HasSubst G)`, and explicit
`(hG : ∀ i, Intertwines ebar ehat (G i))`, in source order.
The result is exactly `Intertwines.substStatement hH hHsubst hGsubst hG`.
Both finiteness hypotheses remain `Finite`; neither is strengthened to
`Fintype`. The coefficient ring and series are the shared published
`LocalField` extending `CompleteDVF` and `LubinTateSeries` interfaces.
The element `π` is arbitrary in the valuation subring, with no additional
uniformizer hypothesis.

## Implemented proof and source correspondence

The initial `change` exposes the body of the published proposition
abbreviation. Unfolding `Intertwines` in `hH` and the goal then reduces the
proof to the source chain of six equalities (lines 240–273):

1. Apply M354.008 `subst_powerSeries_subst` in reverse, using `hHsubst`
   and `hGsubst`, to move substitution by `G` past the outer one-variable
   series `e.toPowerSeries`.
2. Rewrite the resulting inner expression using the given equation `hH`.
3. Apply `MvPowerSeries.subst_comp_subst_apply` to compose the inserted
   family `i ↦ inVariable ebar i` with `G`. M348.003
   `inVariable_hasSubst ebar` supplies the first substitution condition
   using `[Finite σ]`; `hGsubst` supplies the second.
4. Use congruence and function extensionality to evaluate each inserted
   variable by M354.009 `subst_inVariable ebar hGsubst i`. The composed
   family becomes `i ↦ PowerSeries.subst (G i) ebar.toPowerSeries`.
5. Use congruence and function extensionality again, now applying the
   pointwise intertwining equation `hG i`.
6. Apply `MvPowerSeries.subst_comp_subst_apply` in reverse with `hGsubst`
   and `inVariable_hasSubst ehat`. The latter uses `[Finite τ]`. This gives
   the required right side
   `MvPowerSeries.subst (fun j : τ ↦ inVariable ehat j)
     (MvPowerSeries.subst G H)`.

After the initial target-exposing `change`, the proof is the unchanged
source proof. It introduces no recursive intertwiner or formal-group
construction and adds no hypotheses.

## Focused dependencies and verification

The direct imports are:

- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.SubstitutionClosure.U010.Statements`;
- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.SubstitutionClosure.U008.Proofs`;
- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.SubstitutionClosure.U009.Proofs`;
- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.InVariableHasSubst`.

These supply the exact target, M354.008, M354.009 and M348.003 respectively.
The relevant substitution composition laws come from Mathlib through
these published dependencies. No external repository import, replacement
interface or new instance is introduced.

A focused Lake build of this proof and its dependent imports succeeds
with zero errors or warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). A separate development
audit prints the full unapplied theorem type with universes and checks
it against the complete telescope and exact target stated above.
The theorem inspection reports only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

Recursive traversal of the project imports, with Lean comments removed,
finds fourteen dependency modules: the three `Intertwiner` modules
`Definitions`, `Statements` and `InVariableHasSubst`; `Series.Definitions`;
the U008 and U009 statement/proof pairs; `U010.Statements`; the shared
local-field `Basic.Definitions`; and valuation `Basic`,
`Complete.Definitions`, `Complete.Projections` and `Henselian.Definitions`.
Neither M353 (`RecursiveIntertwiner`) nor M354.011 (`U011`) occurs in
this closure, so neither is needed for the successful focused check.
All fourteen imported Lean/Markdown pairs match Library base
`10e541e13546c013d0a33255669805da22b82ac3` byte for byte; the target
and its dependencies are unchanged.

## Modifications and attribution

The adaptations are extraction of this one theorem and proof; addition of
the `Langlands.NYLL` namespace prefix; replacement of the whole
`RecursiveIntertwiner`, `StandardSeries` and formal-group source imports
by the four focused published imports above; expression of the conclusion
through the exact published proposition target with a corresponding
initial `change`; omission of unrelated declarations, unused source
opens, classical decidability and noncomputability section settings;
focused module documentation; and the modified-file header.
The theorem telescope and the remainder of the proof are preserved.
No patch10 edit affects this source module.

The original 2026 copyright, Apache-2.0 release line and author header are
preserved. Existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`
remain unchanged; their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
