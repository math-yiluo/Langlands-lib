# NYLL M353.029: adding a monomial preserves a prescribed linear term

This module defines only the proposition target
`Langlands.NYLL.PortInternal.M353.d029Statement`. It records the exact
signature of the source-private theorem
`LubinTate.SameUniformizer.hasLinearTerm_add_monomial`, lines 503–509
(proof at 509–528) of Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean#L503-L528),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The original file SHA-256 is
`627cad1b4ca585bb98d54d4dc97a88735e737576155b62e00476e824862983f6`.

The original was read from
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Its registered source is `external-lean-reuse-snapshots-2026-10-21`, content
SHA-256 `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
content SHA-256
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The project errata search found no applicable NYLL entry. No patch10 change
applies to this source module.

## Exact parameters and meaning

The implicit section parameters are `{K : Type u} [Field K]`,
`{F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K}`,
`{sigma : Type w} [Fintype sigma]`, with independent universes `u v w`.
The published `LocalField` extends the published `CompleteDVF`; its
`valuationSubring` is the actual chosen valuation subring with its inherited
commutative ring structure. The source's unused implicit `pi` is absent
from this declaration's effective signature.

The retained implicit declaration parameters are
`{H : MvPowerSeries sigma F.valuationSubring}` and
`{L : sigma → F.valuationSubring}`. The explicit parameters, in source order,
are `(hH : HasLinearTerm H L)`, `(d : sigma →₀ ℕ)`,
`(hd : 2 ≤ d.degree)`, and `(c : F.valuationSubring)`.
For these parameters the target is exactly
`HasLinearTerm (H + MvPowerSeries.monomial d c) L`.
Thus adding one monomial of total degree at least two preserves the
specified constant and linear terms in the sense of the published
`HasLinearTerm` predicate, namely order at least two after subtracting
`linearForm L`. The hypotheses `hH` and `hd` are arguments of the target,
not additional assertions proved here.

There is no uniformizer proof, `LubinTateSeries` argument, approximation
bundle, nonempty-variable assumption, or condition on the coefficient `c`.
This unit states a proposition and provides no proof of it. Its exact proof
successor must prove this Library target as
`Langlands.NYLL.PortInternal.M353.d029` before the replacement-step data
uses that proof.

## Modifications, imports, and attribution

Worker 294 extracted this signature on 14 November 2026, replaced the
private source name by `Langlands.NYLL.PortInternal.M353.d029Statement`,
and represented the conclusion by a reducible `abbrev` returning `Prop`.
All binder kinds, order, hypotheses and mathematical types are retained.
The now unused hypothesis variables have their unused-variable lint
suppressed locally; their names and binders are unchanged.

The source imports of `DegreeStabilization` and `RecursiveCorrection`
are replaced by the published `FormalModule.LinearTerm.Definitions` and
`LocalField.DiscreteValuationField.Basic.Definitions` modules. Their exact
`linearForm`, `HasLinearTerm`, `LocalField`, and `LocalField.valuationSubring`
names are reused, and Mathlib supplies `MvPowerSeries`, `monomial`, and
`Finsupp.degree`. Other source declarations and all source proof bodies are
omitted. The focused Lean check establishes that this target needs neither
the recursive series nor the monomial-correction construction. No global
instances or extra mathematical assumptions are introduced.

The original copyright, Apache-2.0 release and author lines are preserved
verbatim; the header gains a modification record and the module description
is replaced. The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`
are unchanged, with respective SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
