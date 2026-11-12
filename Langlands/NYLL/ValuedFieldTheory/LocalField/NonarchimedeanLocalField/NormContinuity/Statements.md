# Continuity targets for finite-dimensional field norms

This module states the two norm-continuity results M255.001–002 as separate
Prop-valued definitions. Both retain the original interface:

```lean
(K : Type u) (L : Type v)
[NontriviallyNormedField K] [NormedField L]
[Algebra K L] [FiniteDimensional K L] [CompleteSpace K]
[ContinuousSMul K L]
```

The field universes `u` and `v` are independent. The algebra structure and its
continuous scalar action are supplied. Completeness is assumed only on `K`;
there is no local-field, Galois, discrete-valuation or separability hypothesis.
The actual topologies are those supplied by the normed-field structures.

`Langlands.NYLL.LocalFieldTheory.algebraNorm_continuous_of_finiteDimensionalStatement K L`
says `Continuous (Algebra.norm K : L → K)` for the actual algebra norm.
`Langlands.NYLL.LocalFieldTheory.normUnits_continuous_of_finiteDimensionalStatement K L`
says `Continuous (Langlands.NYLL.LocalFieldTheory.normUnits K L)`, where
`normUnits` is the published M092.002 definition `Units.map (Algebra.norm K)`.
The unit groups have Mathlib's canonical induced unit topologies. This module
provides targets only; neither continuity proposition is proved here.

## Source correspondence

| Source theorem, unit and start line | Prop-valued target |
| --- | --- |
| `LocalFieldTheory.algebraNorm_continuous_of_finiteDimensional`, M255.001, line 34 | `Langlands.NYLL.LocalFieldTheory.algebraNorm_continuous_of_finiteDimensionalStatement` |
| `LocalFieldTheory.normUnits_continuous_of_finiteDimensional`, M255.002, line 50 | `Langlands.NYLL.LocalFieldTheory.normUnits_continuous_of_finiteDimensionalStatement` |

The exact source is `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormContinuity.lean`,
lines 32–57; its SHA-256 is
`8cd7c49384a442469cff5bf0397150f52b24b03fa3087b3b252b29e9e05b38a8`.
The source is Naganori Yamaguchi's ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, retained under
`literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
The registered original is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum was found in the available project notes.

The extracted statements preserve every source binder, instance, argument order
and proposition. Each theorem signature becomes a `def` returning `Prop` under
its adapted source name followed by `Statement`; the original proof bodies
are removed. The namespace receives the `Langlands.NYLL` prefix, and the
modification notice and focused module documentation are new.

The original `NormUnits` import is replaced by the published focused
`Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions`.
The original `NonarchimedeanLocalField.Basic` import and associated local-field
namespace/scoped openings are omitted. The original Mathlib imports
`Mathlib.Analysis.Normed.Module.FiniteDimension` and
`Mathlib.Topology.Instances.Matrix` are retained. A successful focused
Lean-service build and inspections of both targets confirm that this smaller
NYLL import set suffices, with `statement_returns_prop = true` for each and
both universe parameters retained.

The third source theorem, on valuation-integer units, is outside this pair;
it requires the separately adapted integer-unit inclusion. No proof or
reciprocity assertion is included in this target publication. No global
instances are added.

## Attribution

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi; authors Naganori Yamaguchi (assisted by OpenAI Codex).
The unchanged Apache-2.0 [LICENSE](../../../../../../licenses/NYLL/LICENSE) and [NOTICE](../../../../../../licenses/NYLL/NOTICE) accompany this
subset at `licenses/NYLL/`. Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
These bytes were verified against the carried-license manifest. The original
NOTICE has no source-specific entry for this extracted file. Worker 120 made
the recorded extraction and namespace/import changes on 9 November 2026;
no earlier adaptation or patch10 code is incorporated.
