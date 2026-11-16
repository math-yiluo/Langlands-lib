# Fixed-degree correction data

This pair adapts exactly three source-private data declarations. The other
M353 laws remain separate proposition targets and exact proof successors.

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

| Unit and source lines | Source name | Adapted declaration |
| --- | --- | --- |
| M353.006, 68–82 | `LubinTate.SameUniformizer.correctionStep` | `Langlands.NYLL.PortInternal.M353.d006` |
| M353.007, 84–93 | `LubinTate.SameUniformizer.correctList` | `Langlands.NYLL.PortInternal.M353.d007` |
| M353.013, 256–264 | `LubinTate.SameUniformizer.correctDegree` | `Langlands.NYLL.PortInternal.M353.d013` |

## Parameters and construction

All declarations retain the source context at lines 29–38: independent
universes `u v w`, implicit `{K : Type u}`, `[Field K]`, implicit
`{F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K}`,
implicit `{pi : F.valuationSubring}`, implicit `{sigma : Type w}` and
`[Fintype sigma]`. The shared `LocalField` extends the published `CompleteDVF`;
its valuation subring and valuation are used directly. Both `e` and `ebar`
have the shared type `Langlands.NYLL.LubinTate.LubinTateSeries F pi`.
No global instance is added or replaced, and no universe is identified.
The `Fintype sigma` assumption is preserved; it is not weakened to `Finite`.

For `d006`, the explicit parameters, in order, are `hpi`, `e`, `ebar`,
`hm : 2 ≤ m`, `H : d002 (F := F) L` and
`d : {d : sigma →₀ ℕ // d.degree = m}`; `L` and `m` are implicit.
Here `hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K)` is the exact
source uniformizer assumption. The subtype `d002` consists of series together
with their `HasLinearTerm` proof. The body derives `hd : 2 ≤ d.1.degree`
from `d.2` and `hm`, applies `correctedIntertwiner hpi e ebar H.2 d.1 hd`,
and packages the result with the exact `correctedIntertwiner_hasLinearTerm`
proof. Both components of the subtype value are retained.

For `d007`, the order is `hpi`, `e`, `ebar`, implicit `L`, implicit `m`,
`hm`, the list `ds`, then `H`. Its body is exactly
`ds.foldl (d006 hpi e ebar hm) H`, so the corrections are applied from left
to right. The list may be empty and need not be nodup.

For `d013`, the order is `hpi`, `e`, `ebar`, implicit `L`, `H`, explicit
`m`, then `hm`. It applies `d007` to `d003 (sigma := sigma) m`, the source
list of all degree-`m` exponents. It uses the enumeration data, with no
membership or nodup theorem in its body. All three declarations return
`d002 (F := F) L`, preserving the bundled linear term. Their original
`noncomputable def` status and the enclosing noncomputable section are retained.

## Dependencies and modifications

The focused dependencies are
`RecursiveIntertwiner.Approximation.Definitions` for `d002`,
`RecursiveIntertwiner.DegreeIndexList.Definitions` for `d003`, and the exact
M352.003 proof module `RecursiveCorrection.HasLinearTermProof`, which also
provides `correctedIntertwiner`.
All module names here are below
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule`.
The source imports the full `DegreeStabilization` and `RecursiveCorrection`
modules. This pair uses the smaller direct imports above. The local M353 coefficient
and defect laws are absent from these definition bodies; their independent
proof successors remain obligations.

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

The three definition bodies are preserved after the listed reference renamings;
there is no mathematical change to the correction or fold construction.

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
This checks that the published `d002`, `d003`, `correctedIntertwiner`
and `correctedIntertwiner_hasLinearTerm` suffice for all three bodies;
the full source `DegreeStabilization` module and the local coefficient
theorems are not needed to elaborate these data.
