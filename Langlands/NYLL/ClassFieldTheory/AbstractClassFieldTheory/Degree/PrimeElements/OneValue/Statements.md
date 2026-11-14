# NYLL M028.006: coercion target for the value one

The paired Lean file adapts the statement of
`ClassFormation.ValuationData.oneValue_coe` from Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/PrimeElements.lean`,
M028.006. The source docstring is at line 115, the `simp` attribute at line
116, the theorem telescope and equality at lines 117–118, and the source proof
`rfl` at line 119. The enclosing namespace, opens, noncomputable section and
variables are at lines 16–28, and `namespace ValuationData` at line 107.
The source file SHA-256 is
`9b2f91f76898d32b4f6f556a6b628aa0c4cf40768f43423b15e81de22fadc4bf`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

The registered original source is
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No NYLL-specific erratum was found among the available project errata notes.

## Statement and complete telescope

| Original | Adapted |
| --- | --- |
| `ClassFormation.ValuationData.oneValue_coe` | `Langlands.NYLL.ClassFormation.ValuationData.oneValue_coeStatement` |
| `ClassFormation.ValuationData.oneValue` | `Langlands.NYLL.ClassFormation.ValuationData.oneValue` (M028.005) |
| `ClassFormation.ValuationData` | `Langlands.NYLL.ClassFormation.ValuationData` (M025.012) |
| `ClassFormation.DegreeData` | `Langlands.NYLL.ClassFormation.DegreeData` (M010.002) |
| `ClassFormation.ZHat` | `Langlands.NYLL.ClassFormation.ZHat` (M008.008) |
| `IntegralRepGroupType` | `Langlands.NYLL.IntegralRepGroupType` |

The binders are implicit `{G : Langlands.NYLL.IntegralRepGroupType}`,
`[Group G]`, `[TopologicalSpace G]`, `{D : DegreeData G}` and
`{A : Rep ℤ G}`, followed by the explicit `v : ValuationData D A`, exactly
as in the source. The group lies in `Type 0`; the carrier of `A` has an
arbitrary universe, the single universe parameter.

```lean
def oneValue_coeStatement (v : ValuationData D A) : Prop :=
  (v.oneValue : ZHat) = 1
```

It states that the value-group element `v.oneValue`, coerced to the
ambient `ZHat`, is `1`. There is no further hypothesis.

## Modification record

Worker 110 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the adapted names in the table.
2. Replace `theorem oneValue_coe … : equality := rfl` by
   `def oneValue_coeStatement … : Prop := equality`. The equality is copied
   verbatim. The source proof and `@[simp]` attribute are omitted: this
   contribution publishes a proposition target, and a proof is separate work.
3. Replace the source docstring (line 115) by a description of the
   proposition that names its source theorem, and replace the source module
   docstring by a description of this module with a modification notice.
4. Replace the source import of `Degree.ValuationLaws` by the focused import
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.OneValue.Definitions`.
5. Omit the unused `open KummerTheory` and `open CyclicCohomology`. Retain
   the noncomputable section, the group-variable comment and both variable
   lines. Omit all other source units; no helper declaration or instance is
   added.

This is the exact source equality as a named `Prop`, without a published
proof. It discharges no host class-formation, cup, transfer, Tate or
reciprocity target.

## Verification

The module passed a project Lean service check on 14 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, with no errors or warnings.
Declaration inspection reported `statement_returns_prop: true`, one universe
parameter, and the axioms `propext`, `Classical.choice` and `Quot.sound`. A
private probe assigned the unapplied target to its full expected telescope at
an arbitrary carrier universe `u`, and checked by reflexivity that its body is
exactly the source equality. Compilation and inspection are separate from
independent semantic acceptance and publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
