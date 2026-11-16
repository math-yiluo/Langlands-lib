# Lower-coefficient preservation targets

This pair states the three source laws that a fixed-degree correction leaves
all lower-degree power-series coefficients unchanged. It contains Prop-valued
definitions, and makes no claim that the laws have been proved.

## Original source

Naganori Yamaguchi (assisted by OpenAI Codex),
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`.
The file SHA-256 is
`627cad1b4ca585bb98d54d4dc97a88735e737576155b62e00476e824862983f6`.
The readable original is beneath
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
`nyll-classfieldtheory-fbd320cd-supplement` supplies attribution and
verification-file context. The source has no patch10 edits.

| Unit | Source signature / full proof lines | Adapted target | Exact proof name |
| --- | --- | --- | --- |
| M353.008 | 95–104 / 95–113 | `Langlands.NYLL.PortInternal.M353.d008Statement` | `Langlands.NYLL.PortInternal.M353.d008` |
| M353.009 | 115–124 / 115–140 | `Langlands.NYLL.PortInternal.M353.d009Statement` | `Langlands.NYLL.PortInternal.M353.d009` |
| M353.014 | 266–274 / 266–276 | `Langlands.NYLL.PortInternal.M353.d014Statement` | `Langlands.NYLL.PortInternal.M353.d014` |

## Exact targets

All declarations retain the source context at lines 29–38: independent
universes `u v w`, implicit `{K : Type u}`, `[Field K]`, implicit
`{F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K}`,
implicit `{pi : F.valuationSubring}`, implicit `{sigma : Type w}` and
`[Fintype sigma]`. The shared `LocalField` extends the published `CompleteDVF`;
its valuation subring and valuation are used directly. Both `e` and `ebar`
have the shared type `Langlands.NYLL.LubinTate.LubinTateSeries F pi`.
No global instance is added or replaced, and no universe is identified.
The `Fintype sigma` assumption is preserved; it is not weakened to `Finite`.

Every target keeps the explicit uniformizer proof
`hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K)`, explicit `e ebar`,
implicit `L`, the bundled approximation `H`, and `hm : 2 ≤ m`.
For `d008Statement` and `d009Statement`, `m` is implicit; for
`d014Statement`, it is explicit and follows `H`. The strict degree premise
`hq : q.degree < m` is an explicit argument in all three targets, even
though the proposition body only refers to `q` and `m`.

The `d008Statement` parameter order after `hm` is `H`, the corrected degree-`m`
index `d`, the arbitrary exponent `q`, then `hq`. Its conclusion is
`MvPowerSeries.coeff q (d006 hpi e ebar hm H d).1 = MvPowerSeries.coeff q H.1`.

The `d009Statement` order after `hm` is the list `ds`, `H`, `q`, then `hq`.
Its conclusion replaces `d006` by `d007 hpi e ebar hm ds H`.
There is no nodup, membership or nonmembership premise.

The `d014Statement` order after implicit `L` is `H`, `m`, `hm`, `q`, then `hq`.
Its conclusion uses `d013 hpi e ebar H m hm`.
All comparisons concern coefficients of the underlying series, selected
by `.1` from the bundled approximation.

## Dependencies and modifications

The sole direct import is
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.CorrectionData`.
It supplies the adapted correction definitions and their type dependencies.
The source theorem commands become `def ...Statement ... : Prop := ...`;
their proof terms are omitted and all explicit/implicit binders and hypotheses
are retained in source order. Each target needs its separate exact proof
successor after target publication. The source routes are the single-monomial
coefficient formula for M353.008, list induction using .008 for .009,
and specialization of .009 to the complete list for .014; these are a
successor dependency plan, not a proof provided by this pair.

Source-private names are exposed under `Langlands.NYLL.PortInternal.M353`.
The source context is moved inside `namespace Langlands.NYLL` with
`open LocalFieldTheory.DiscreteValuationField` and
`open LubinTate LubinTate.SameUniformizer`, then `namespace PortInternal.M353`.
The source references `Approximation`, `degreeIndexList`, `correctionStep`,
`correctList` and `correctDegree` become `d002`, `d003`, `d006`, `d007` and
`d013`. The public `correctedIntertwiner`, its linear-term preservation law,
and `defect` retain their source spellings under `Langlands.NYLL`.
The original copyright, Apache-2.0 release line and author header are preserved;
a separate modified-file notice and focused module/doc comments are added.
Existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are unchanged.

The file disables `linter.unusedVariables` to preserve the original explicit
hypothesis names, including proofs not referenced by a proposition body.
This option changes only lint diagnostics.

## Scope and dependencies

The data use the published exact M352.003
`Langlands.NYLL.LubinTate.SameUniformizer.correctedIntertwiner_hasLinearTerm`
from `RecursiveCorrection.HasLinearTermProof`. The proposition targets do
not supply their seven exact proofs. Those require separate proof successors.
In particular, M353.012 needs M352.004 cancellation, and M353.015 needs
the degree-list nodup and membership theorems, only in their proof successors.

A focused check on 16 November 2026 compiled this module with these
imports in the approved Lean 4.34.0 / Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` environment without diagnostics.
Every target in this pair was inspected as Prop-valued with independent
universe parameters `u`, `v`, `w`. These development checks establish
elaboration and proposition shape; they do not supply the exact proofs.
