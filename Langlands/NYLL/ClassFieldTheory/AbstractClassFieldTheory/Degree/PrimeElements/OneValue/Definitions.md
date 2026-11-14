# NYLL M028.005: the value one in the value group

The paired Lean file adapts one data definition from Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/PrimeElements.lean`.
The pinned source file has SHA-256
`9b2f91f76898d32b4f6f556a6b628aa0c4cf40768f43423b15e81de22fadc4bf`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No NYLL-specific erratum was found among the available project errata notes.

## Source correspondence

| Unit | Source declaration | Docstring | Command | Adapted declaration |
| --- | --- | --- | --- | --- |
| M028.005 | `ClassFormation.ValuationData.oneValue` (def) | 109 | 110–113 | `Langlands.NYLL.ClassFormation.ValuationData.oneValue` |

The enclosing source context is `namespace ClassFormation` (line 16),
`open KummerTheory` (line 18), `open CyclicCohomology` (line 20),
`noncomputable section` (line 24), the comment and variables at lines 26–28,
and `namespace ValuationData` (line 107). The source docstring is retained
verbatim.

The definition uses the published `Langlands.NYLL.ClassFormation`
declarations `ValuationData` (M025.012, with its field `integers_mem`),
`ValuationData.valueGroup` (M025.013), `DegreeData` (M010.002) and `ZHat`
(M008.008), and `Langlands.NYLL.IntegralRepGroupType`.

## Object and complete telescope

The binders are the source section variables: implicit
`{G : Langlands.NYLL.IntegralRepGroupType}`, `[Group G]`,
`[TopologicalSpace G]`, `{D : DegreeData G}` and `{A : Rep ℤ G}`, followed by
the explicit `v : ValuationData D A`. The group lies in `Type 0`; the carrier
of `A` has an arbitrary universe, the single universe parameter.

```lean
def oneValue (v : ValuationData D A) : v.valueGroup :=
  ⟨1, by
    obtain ⟨a, ha⟩ := v.integers_mem 1
    exact ⟨a, by simpa using ha⟩⟩
```

The result is the element `1 : ZHat` of the value group `Z = v(A_k)`,
bundled as a subtype element. Its membership proof is the source proof: the
structure field `integers_mem` at `m = 1` supplies `a` with
`v.toAddMonoidHom a = (Int.castRingHom ZHat) 1`, and `simpa` rewrites the
cast of `1` to `1`. The underlying value is the literal `1`; only the proof
depends on `v`.

## Modification record

Worker 110 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the published names above.
2. Replace the source import of `Degree.ValuationLaws` (line 7) by the
   focused import
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Definitions`,
   which supplies `ValuationData` and `ValuationData.valueGroup`.
3. Omit the unused `open KummerTheory` and `open CyclicCohomology`. Retain
   the noncomputable section, the group-variable comment and both variable
   lines. Replace the source module docstring by a description of this module
   with a modification notice.
4. Extract only this definition; its kind, binders, type, body and
   embedded proof are unchanged. All other source units are omitted, including
   M028.006 (`oneValue_coe`, whose statement is in the paired
   `OneValue.Statements` module). No helper declaration or instance is added.

Exact-name searches of the Library found no existing declaration of this
name. This support module discharges no host class-formation, cup, transfer,
Tate or reciprocity target.

## Verification

The module passed a project Lean service check on 14 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, with no errors or warnings.
Declaration inspection reported one universe parameter and the axioms
`propext`, `Classical.choice` and `Quot.sound`. A private probe assigned the
unapplied constant to its full expected telescope at an arbitrary carrier
universe `u`. Compilation and inspection are separate from independent
semantic acceptance and publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
