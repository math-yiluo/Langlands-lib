# Same-degree defect preservation targets

This pair states that corrections preserve a same-degree defect coefficient
when its index is not corrected. These are proposition targets only.

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
| M353.010 | 142–152 / 142–163 | `Langlands.NYLL.PortInternal.M353.d010Statement` | `Langlands.NYLL.PortInternal.M353.d010` |
| M353.011 | 165–176 / 165–202 | `Langlands.NYLL.PortInternal.M353.d011Statement` | `Langlands.NYLL.PortInternal.M353.d011` |

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

Both targets preserve explicit `hpi`, `e`, `ebar`, implicit `L`, implicit `m`,
and explicit `hm : 2 ≤ m`. The exact type of `hpi` is
`F.toCompleteDVF.valuation.IsUniformizer (pi : K)`.

For `d010Statement`, the remaining order is `H`, two indices
`q d : {d : sigma →₀ ℕ // d.degree = m}`, then `hqd : q ≠ d`.
The conclusion compares the `q.1` coefficient of
`defect e ebar (d006 hpi e ebar hm H d).1` with that of `defect e ebar H.1`.
The disequality is between subtype indices, exactly as in the source;
it is not a premise on unrelated degrees.

For `d011Statement`, the remaining order is the correction list `ds`, `H`,
the degree-`m` index `q`, then `hq : q ∉ ds`. The conclusion compares
`defect e ebar (d007 hpi e ebar hm ds H).1` with `defect e ebar H.1`
at `q.1`. The list has no nodup premise. Neither target asserts that any
coefficient vanishes or covers a corrected index.

## Dependencies and modifications

The direct imports are
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.CorrectionData`
and `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions`.
The latter provides the shared literal substitution defect.
The source theorem commands become Prop-valued `def ...Statement`
declarations with unchanged parameter order, binder modes, hypotheses and
conclusions after renaming. Their proof terms are not included.
M353.010's proof successor needs the published exact M351.026
`coeff_defect_add_monomial_eq_of_degree_le`; M353.011's successor uses
list induction and the exact .010 proof. These are proof obligations,
not assumptions added to either target.

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
