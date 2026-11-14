# NYLL M354.008: Mixed power-series substitution

This file publishes the exact Prop-valued target
`Langlands.NYLL.LubinTate.SameUniformizer.subst_powerSeries_substStatement`.
It does not supply its proof.

## Source

Naganori Yamaguchi, [`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/StandardFormalGroup.lean#L199),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/StandardFormalGroup.lean`, lines 199–212; original declaration
`LubinTate.SameUniformizer.subst_powerSeries_subst`.
Original file SHA-256: `c563068d157ec2664f0e81603050248add1d49e955b55b5a380a5322d4f3415d`.
The original is readable at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/StandardFormalGroup.lean`.
The registered sources are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable NYLL erratum was found in the current Library's `notes/errata/`.

## Exact scope and source correspondence

The theorem signature becomes the telescope of an `abbrev` returning `Prop`;
its body is precisely the source conclusion. For a multivariable series `H`, a family `G`, and a one-variable series `f`, the two orders of substitution agree. The explicit arguments `hH : PowerSeries.HasSubst H` and `hG : MvPowerSeries.HasSubst G` and the explicit final argument `f` are retained. Neither variable type is required to be finite; `π` is not a parameter of this declaration because it does not occur in its type.

The source section context (lines 29–39 and 192–195) is retained with independent
universes `u v w w'`, implicit `K : Type u`, `[Field K]`, implicit
`F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K`,
and implicit `π : F.valuationSubring`. The variable types `σ : Type w`
and `τ : Type w'` have independent universes. Only section parameters used by
the source declaration enter the target's telescope. In particular, `π` is an
arbitrary element of the valuation subring, without a uniformizer assumption.
The field and Lubin–Tate interfaces, where needed, are the single shared
published `LocalField` extending `CompleteDVF` and the published
`LubinTateSeries`; no replacement interface or instance is introduced.

## Focused imports and proof route

Direct imports are:

- `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions`;
- `Mathlib.RingTheory.PowerSeries.Substitution`;

They provide the mathematical constants in this target without the source's
whole `RecursiveIntertwiner`, `StandardSeries`, or formal-group modules.
The source proof changes `PowerSeries.subst H f` to substitution of the constant `Unit`-indexed family with value `H`, then applies `MvPowerSeries.subst_comp_subst_apply hH.const hG f`. Thus M354.008 is a wrapper around that existing Mathlib theorem, with the exact source local-field coefficient ring. The proof successor should preserve that correspondence.

M354.011 is excluded from this selected closure: none of the five selected
signatures uses it, the source .010 proof precedes it, the .012 proof calls
.010 directly, and the .008/.009/.013 proof routes above use only substitution
and elementary insertion laws. A focused `lean_check` of this target succeeded with zero errors and warnings
and `statement_returns_prop: true`, using environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Its imports include neither
M353 nor M354.011. Proof-successor checks must separately verify their imports.

## Complete modification and attribution record

The modifications are extraction of this one signature and conclusion; replacement
of `theorem` by a reducible Prop-valued `abbrev` with suffix `Statement`; addition
of the `Langlands.NYLL` namespace prefix; the focused imports listed above;
omission of the proof, other declarations and unused source opens/noncomputability
settings; replacement of the module and declaration documentation by target
wording; and the modified-file header. All source binder names, order, visibility,
universes, finite-variable instances, and mathematical hypotheses are retained.
The unused-variable linter alone is disabled so that the source proof-argument
names can be kept even though a proposition target's conclusion does not use them.
There are no patch10 modifications to this source module.

The original 2026 copyright, Apache-2.0 release line and authorship header are
preserved. Existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are
unchanged; their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
