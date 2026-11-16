# NYLL M353.032: one replacement sets the selected coefficient

The theorem `Langlands.NYLL.PortInternal.M353.d032` proves the published
proposition `Langlands.NYLL.PortInternal.M353.d032Statement` from
`Replacement.StepStatements`. It is adapted from Naganori Yamaguchi's
private theorem `LubinTate.SameUniformizer.coeff_replacementStep_self`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`,
lines 556–564, at commit
`fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`.

The readable pinned original is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`.
Its file SHA-256 is
`627cad1b4ca585bb98d54d4dc97a88735e737576155b62e00476e824862983f6`.
The registered snapshot collection `external-lean-reuse-snapshots-2026-10-21`
has content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
`nyll-classfieldtheory-fbd320cd-supplement` registers the same pinned project.
No applicable NYLL erratum was found in the Library's `notes/errata/`.

## Exact statement and implemented proof

The theorem retains the effective source section parameters from lines
29–38: implicit `{K : Type u} [Field K]`, `{F : LocalField.{u, v} K}`,
and `{sigma : Type w} [Fintype sigma]`. The universes `u`, `v` and `w`
are independent. These are followed by implicit `L` and `m`, then explicit
`hm : 2 ≤ m`, `target`, `H : d002 (F := F) L`, and
`d : {d : sigma →₀ ℕ // d.degree = m}`, in source order.
The source section parameter `pi` does not occur in this theorem.
There is no uniformizer witness or `LubinTateSeries` parameter.

The conclusion is exactly

```text
MvPowerSeries.coeff d.1 (d030 hm target H d).1 =
  MvPowerSeries.coeff d.1 target.
```

Here `target` is an arbitrary series over the actual valuation subring
of `F`, and `H` belongs to the published prescribed-linear-term subtype
`d002 L`. The published construction `d030` adds to `H.1` the monomial
at `d.1` with coefficient
`MvPowerSeries.coeff d.1 target - MvPowerSeries.coeff d.1 H.1`.

The proof first exposes the equality with `change`. It then simplifies
`d030`, uses additivity of coefficients and
`MvPowerSeries.coeff_monomial_same`, and cancels the old coefficient
against its subtraction. This is the source proof at line 564 after
renaming `replacementStep` to `d030`, with the initial `change` accounting
for the published Statement abbreviation. No coefficient nonvanishing
or prescribed-linear-term condition on `target` is assumed.

## Adaptations and attribution

Naganori Yamaguchi (assisted by OpenAI Codex) is the original author.
Worker 294 prepared the source adaptation in the shared revision-2
draft for Task 6116
(`c6ac604a-2c1d-4aae-94b5-181c90f66897`):
qualified namespaces, renamed the source-private theorem and references
to the public port-internal names `d032`, `d002` and `d030`, stated the
conclusion using `d032Statement`, and added the initial `change`.
The original broad `DegreeStabilization` and `RecursiveCorrection`
imports were replaced by the focused published
`Replacement.StepStatements` import. The extracted proof needs no
noncomputable section.

Worker 295 reused that complete proof preparation, checked the source
signature and proof against the pinned original, expanded this source
and attribution record, and prepared the focused submission and Lean
service checks. Worker 294 is credited as coauthor of this contribution.
The mathematical proof body from Worker 294's draft is retained.
The Statement pair and all imported Lean/Markdown pairs remain unchanged.
No patch10 edit affects the original source module.

The original copyright, Apache-2.0 release and authorship header is
retained verbatim. The existing `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
remain byte-for-byte unchanged.
