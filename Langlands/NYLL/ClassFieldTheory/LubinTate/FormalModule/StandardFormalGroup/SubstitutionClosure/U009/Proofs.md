# NYLL M354.009: Substitution into an inserted variable proof

The theorem
`Langlands.NYLL.LubinTate.SameUniformizer.subst_inVariable`
proves exactly the published target
`Langlands.NYLL.LubinTate.SameUniformizer.subst_inVariableStatement`.
It states
`MvPowerSeries.subst G (inVariable e i) =
PowerSeries.subst (G i) e.toPowerSeries`.

## Source and scope

Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`, StandardFormalGroup.lean, lines 216–224](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/StandardFormalGroup.lean#L216),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, supplies the theorem
and implemented proof. The original declaration is
`LubinTate.SameUniformizer.subst_inVariable`. The original file SHA-256 is
`c563068d157ec2664f0e81603050248add1d49e955b55b5a380a5322d4f3415d`.
The pinned source is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Its registered sources are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

The theorem retains independent universes `u v w w'` and the full source
telescope, in order: implicit `{K : Type u}`, `[Field K]`, implicit
`{F : LocalField.{u,v} K}`, `{π : F.valuationSubring}`,
`{σ : Type w}`, `{τ : Type w'}`, explicit
`(e : LubinTateSeries F π)`, implicit
`{G : σ → MvPowerSeries τ F.valuationSubring}`, explicit
`(hG : MvPowerSeries.HasSubst G)` and `(i : σ)`.
The result type is precisely `subst_inVariableStatement e hG i`.
Neither variable type has a finiteness assumption, and `π` is an arbitrary
element of the valuation subring. The shared published `LocalField`
interface extending `CompleteDVF` and the published `LubinTateSeries` and
`inVariable` definitions are reused without modification.

## Implemented proof

A preliminary `change` exposes the equality in the published target
abbreviation; this is a definitional equality. The following three proof
lines are unchanged from source lines 222–224.
First, `rw [inVariable]` exposes insertion as
`PowerSeries.subst (MvPowerSeries.X i) e.toPowerSeries`.
Second, the published M354.008 theorem
`subst_powerSeries_subst (PowerSeries.HasSubst.X i) hG`
moves the multivariable substitution through this one-variable substitution.
The supplied `PowerSeries.HasSubst.X i` is the required substitution
hypothesis for the variable `X i`.
Finally, `simp [MvPowerSeries.subst_X hG]` replaces substitution into
`X i` by `G i`, obtaining the target equality.
The M354.008 proof itself uses Mathlib's
`MvPowerSeries.subst_comp_subst_apply`.
No new convergence argument or recursive intertwiner construction is used.

## Imports and verification

The two direct imports are:

- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.SubstitutionClosure.U009.Statements`;
- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.SubstitutionClosure.U008.Proofs`.

The first supplies the exact target and the definition of `inVariable`.
The second supplies mixed substitution. Tracing all transitive project
imports reaches, besides these two modules, U008's `Statements`,
`Intertwiner.Definitions`, `Series.Definitions`, local-field
`Basic.Definitions`, and valuation `Complete.Projections`,
`Complete.Definitions`, `Henselian.Definitions` and `Basic`.
The substitution laws come from Mathlib's
`RingTheory.PowerSeries.Substitution` and
`RingTheory.MvPowerSeries.Substitution`.
Consequently neither M353 (`RecursiveIntertwiner`) nor M354.011
(`Intertwines.reindex`) occurs in the dependent imports of the successfully
compiled focused proof. The proof uses no M348 elementary theorem.

The approved checking environment is
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
Focused compilation of the proof and its imports succeeds with zero errors
and warnings. Declaration inspection reports the four independent universe
parameters `u v w w'` and only `propext`, `Classical.choice` and `Quot.sound`
as assumptions. A separate private check assigns the unapplied theorem
constant directly to the full required telescope and prints its type with
universe levels; it also succeeds with zero errors and warnings.
All ten transitive project dependency Lean/Markdown pairs and both license
files were compared byte for byte with the Library base and are unchanged.

## Adaptations and attribution

The adaptations are extraction of this one theorem and proof; addition of
the `Langlands.NYLL` namespace prefix; replacement of the whole source
module imports by the two focused published imports above; expression of
the conclusion using the exact published target abbreviation and a preliminary
`change` exposing its equality; omission of
unrelated declarations, unused source opens, classical decidability and
noncomputability settings; focused module and declaration documentation;
and the modified-file header. All source universes, binder order and
visibility, mathematical hypotheses and proof steps are preserved.
No patch10 edit affects this source module.

The original 2026 copyright, Apache-2.0 release line and author header are
preserved. Existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`
are unchanged; their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
