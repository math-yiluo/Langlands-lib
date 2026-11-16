# NYLL M351.013: the linear model admits substitution

`Langlands.NYLL.PortInternal.M351.d013` proves the published target
`Langlands.NYLL.PortInternal.M351.d013Statement (σ := σ) π`, namely
`MvPowerSeries.HasSubst (d011 (σ := σ) π)`, where
`d011 π i = MvPowerSeries.C π * MvPowerSeries.X i`.

Its full telescope is `{K : Type u} [Field K]`,
`{F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K}`,
`{σ : Type w}`, `[Finite σ]`, and `(π : F.valuationSubring)`, in that order.
The field, value-group and variable universes remain independent. The element
`π` is arbitrary in the valuation subring; there is no uniformizer hypothesis.
The theorem names `σ` explicitly in its result since `π` does not determine it.

## Original source and correspondence

Naganori Yamaguchi,
[`Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, lines 415–421:
the source-private theorem
`LubinTate.SameUniformizer.linearInVariableStabilization_hasSubst`
(M351.013). Its prerequisite
`linearInVariableStabilization_constantCoeff` (M351.012) is at lines 405–413,
and the linear-model definition is at lines 400–403. The file SHA-256 is
`2f7826dadbd3779d2986fcc42611d26f5da79c097cd0e2bdb6d0e8776c1ee717`.
The retained source is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean`.

The registered sources are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable NYLL erratum was found in the published errata notes.

The adapted theorem keeps the source's elaborated hypotheses and conclusion.
In particular, the source explicitly omits its section instance `[Fintype σ]`
and adds `[Finite σ]`; the adapted theorem does the same by declaring only
`[Finite σ]`. The source-private model is the published `d011`, and its
conclusion is expressed through the published reducible target.

## Implemented proof and dependencies

The proof applies `MvPowerSeries.hasSubst_of_constantCoeff_zero` to the
family `i ↦ d011 π i`. Mathlib uses `[Finite σ]` to supply the finite-support
condition of `HasSubst`. Each constant coefficient is zero, hence nilpotent.

The private lemma `constantCoeff_linearModel_for_subst` supplies this last
fact with the source M351.012 proof: unfold `d011`, use multiplicativity of
`MvPowerSeries.constantCoeff`, evaluate the constant series at `π`, rewrite
the constant coefficient of `X_i` as its coefficient at zero, apply
`MvPowerSeries.coeff_zero_X`, and finish with `mul_zero`.

The only direct import is
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LinearModel.Statements`.
Its published imports supply `d011`, `LocalField`, the valuation subring and
Mathlib's power-series substitution machinery. No unpublished proof is
required. The elementary prerequisite is private under a fresh name, as
permitted by Task 6850; this module does not define the separately assigned
public theorem `Langlands.NYLL.PortInternal.M351.d012`.

## Modifications and license

Worker 791, 16 November 2026: extract M351.013 into the focused `HasSubst`
module; rename the source-private theorem to the prescribed public `d013`;
replace the source model name by `d011`; state the theorem through its
published target with explicit `σ`; and prove M351.012 privately under a
fresh name. The two proof bodies follow the source. Replace the source imports
by the focused published statement module, qualify the opened namespace,
omit unused source section settings and declarations, and adapt documentation.
No published statement, definition or imported file is edited.

The original 2026 copyright, Apache-2.0 release line and author header are
preserved verbatim, with an explicit modification notice.
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain unchanged; their
SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
