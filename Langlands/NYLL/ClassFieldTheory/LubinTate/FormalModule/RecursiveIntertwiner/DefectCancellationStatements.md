# Fixed-degree defect cancellation targets

This pair states cancellation at indices in a nodup correction list and at
every index of a fully corrected degree. It contains statements, not proofs.

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
| M353.012 | 204–215 / 204–254 | `Langlands.NYLL.PortInternal.M353.d012Statement` | `Langlands.NYLL.PortInternal.M353.d012` |
| M353.015 | 278–286 / 278–297 | `Langlands.NYLL.PortInternal.M353.d015Statement` | `Langlands.NYLL.PortInternal.M353.d015` |

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

Both targets keep explicit
`hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K)`, `e`, `ebar`, and
implicit `L`, along with `H : d002 (F := F) L`.

For `d012Statement`, `m` is implicit and the remaining source order is
`hm : 2 ≤ m`, the list `ds`, `H`, `hds : ds.Nodup`, a degree-`m` index `q`,
then `hq : q ∈ ds`. Its exact conclusion is
`MvPowerSeries.coeff q.1 (defect e ebar (d007 hpi e ebar hm ds H).1) = 0`.
The nodup and membership proofs remain explicit target arguments.
No condition on lower coefficients of the defect is imposed.

For `d015Statement`, the source order after implicit `L` is `H`, explicit
`m`, `hm : 2 ≤ m`, arbitrary `q : sigma →₀ ℕ`, then `hq : q.degree = m`.
Its conclusion is
`MvPowerSeries.coeff q (defect e ebar (d013 hpi e ebar H m hm).1) = 0`.
The queried exponent is not replaced by a subtype in the target signature.
The complete enumeration is part of `d013`'s construction; no list premise
is added to .015.

## Dependencies and modifications

The direct imports are
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.CorrectionData`
and `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions`.
Both source theorem commands become `def ...Statement ... : Prop := ...`,
with the source proof terms omitted and every parameter/hypothesis retained
in order. The exact .012 proof successor needs M352.004's
`coeff_defect_correctedIntertwiner_eq_zero` and .011's preservation proof.
The exact .015 successor needs .012 and the independently published .004/.005
nodup/membership proofs for the full degree-index list. These dependencies
are not extra premises in the targets.

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
