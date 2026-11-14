# NYLL M354.008: Mixed power-series substitution proof

The theorem
`Langlands.NYLL.LubinTate.SameUniformizer.subst_powerSeries_subst`
proves exactly the published target
`Langlands.NYLL.LubinTate.SameUniformizer.subst_powerSeries_substStatement`.
It states
`MvPowerSeries.subst G (PowerSeries.subst H f) =
PowerSeries.subst (MvPowerSeries.subst G H) f`.

## Source and scope

Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`, StandardFormalGroup.lean, lines 199–212](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/StandardFormalGroup.lean#L199),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, is the source of the
theorem and implemented proof. The original declaration is
`LubinTate.SameUniformizer.subst_powerSeries_subst`.
Original file SHA-256:
`c563068d157ec2664f0e81603050248add1d49e955b55b5a380a5322d4f3415d`.
The readable pinned source is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Its registrations are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

The theorem preserves four independent universes `u v w w'`, implicit
`{K : Type u} [Field K] {F : LocalField.{u,v} K}`, implicit
`{σ : Type w} {τ : Type w'}`, implicit `H`, explicit
`hH : PowerSeries.HasSubst H`, implicit `G`, explicit
`hG : MvPowerSeries.HasSubst G`, and explicit `f`. Its result is the
unmodified target abbreviation applied to `hH hG f`. Neither variable type
has a finiteness assumption. The unused source section variable `π` is
absent from the theorem telescope, as it is from the original theorem.
The coefficient ring is the valuation subring of the shared published
`LocalField` interface extending `CompleteDVF`.

## Implemented proof

`PowerSeries` is the `Unit`-variable case of `MvPowerSeries`, and
`PowerSeries.subst H f` is definitionally
`MvPowerSeries.subst (fun _ : Unit => H) f`.
The `change` step unfolds the target and uses this definitional equality
on both sides. `PowerSeries.HasSubst.const` converts `hH` into the
multivariable `HasSubst` hypothesis for that constant `Unit`-indexed family.
The proof then applies
`MvPowerSeries.subst_comp_subst_apply hH.const hG f`.
Here Mathlib's first family is `fun _ : Unit => H`, its second family is
`G`, and its resulting composed family is
`fun _ : Unit => MvPowerSeries.subst G H`.
This is exactly the original source proof; no new substitution or
convergence argument is introduced.

## Imports and verification

The sole direct import is
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.SubstitutionClosure.U008.Statements`.
That published module directly imports
`Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions`
and `Mathlib.RingTheory.PowerSeries.Substitution`. The latter imports the
multivariable substitution theorem. No external repository import or new
interface is used.

The proof is checked in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
A focused `lean_check` of the shared local-field definitions, the published
target and this proof succeeded with zero errors and warnings; theorem
inspection reports independent universe parameters `u v w w'` and only
`propext`, `Classical.choice` and `Quot.sound` as assumptions.
A separate private check assigns the unapplied theorem constant directly
to the full required telescope and prints its type with universe levels;
it also succeeds with zero errors and warnings.
Tracing every project import from this proof reaches only the U008 target
and the five valuation/local-field support modules: local-field
`Basic.Definitions`, valuation `Complete.Projections`,
`Complete.Definitions`, `Henselian.Definitions` and `Basic`.
Consequently neither M353 (`RecursiveIntertwiner`) nor M354.011
(`Intertwines.reindex`) belongs to the proof's dependent imports or is
needed for this successful focused check. The statement and all paired
project dependencies were also compared byte for byte with the Library
base and remain unchanged.

## Adaptations and attribution

The modifications are extraction of this one theorem and proof; addition of
the `Langlands.NYLL` namespace prefix; replacement of the original whole
module imports by the focused published statement import; expression of the
result as the exact published target abbreviation; omission of unrelated
declarations, unused section variables, source opens, classical decidability
and noncomputability settings; focused module documentation; and the
modified-file header. The mathematical telescope, conclusion and proof
route are preserved. No patch10 edit affects this source module.
The published statement pair and its dependencies are unchanged.

The original 2026 copyright, Apache-2.0 release line and authorship header
are preserved. Existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`
are unchanged; their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
