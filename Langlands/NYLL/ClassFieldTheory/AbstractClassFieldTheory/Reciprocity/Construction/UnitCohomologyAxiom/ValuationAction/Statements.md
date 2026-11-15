# NYLL M032.018: Galois invariance of the normalized valuation

The paired Lean file adapts the statement of one theorem from Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean`.
The pinned source file has SHA-256
`05d5b39af345bdd78e2dd123f2bc5ef882e52c5d66696c60acde3e8554079ec5`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M032.018 | `ClassFormation.ValuationData.valuationAt_normalExtensionAction` | 196–198 | 199–207 | 208–255 | `Langlands.NYLL.ClassFormation.ValuationData.valuationAt_normalExtensionActionStatement` |

The enclosing source context is `namespace ClassFormation` (line 18),
`open KummerTheory` (line 20), `open CyclicCohomology` (line 22),
`noncomputable section` (line 26), the comment and variables at lines
105–107 (after `section Generic`, lines 32–103), and the first
`namespace ValuationData` (lines 194–327).

The names used in the statement resolve to published `Langlands.NYLL`
declarations: `ClassFormation.ValuationData` (M025.012) and
`ClassFormation.ValuationData.valuationAt` (M025.025, in
`Degree.Valuation.ValuationData.Normalized.Definitions`),
`ClassFormation.normalExtensionAction` (M026.011, in
`Degree.NormLaws.Definitions`), `CyclicCohomology.extensionSubgroup`
(M004.002, the abbreviation `L.toSubgroup.subgroupOf K.toSubgroup`, in
`GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`, hence
the source open of `CyclicCohomology`),
`ClassFormation.FiniteAbstractFieldExtension` (M010.130, in
`Degree.Fields.FiniteAbstractField.Extension.Definitions`) with its fields
`field`, `base` and `below`, `ClassFormation.FiniteAbstractField` (M010.121)
with its field `field`, `ClassFormation.DegreeData` (M010.002),
`KummerTheory.ambientFixedAddSubgroup` (M023.001) and
`IntegralRepGroupType` (M002.001). `Subgroup.Normal`,
`ClosedSubgroup.toSubgroup`, the coercion of a subgroup to a type and `Rep`
are Mathlib's.

## Target and complete telescope

The target has the section binders implicit
`{G : Langlands.NYLL.IntegralRepGroupType}`, `[Group G]`,
`[TopologicalSpace G]`, `{D : DegreeData G}` and `{A : Rep ℤ G}`, followed by
the explicit binders shown. The group lies in `Type 0`; the carrier of `A`
has an arbitrary universe, the single universe parameter.

```lean
def valuationAt_normalExtensionActionStatement
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup E.base.field E.field.field E.below).Normal)
    (k : E.base.field.toSubgroup)
    (a : ambientFixedAddSubgroup A E.field.field) : Prop :=
    v.valuationAt E.field
        (normalExtensionAction A E.base.field E.field.field E.below
          hnormal k a) =
      v.valuationAt E.field a
```

Let `E` be a finite tower `L | K` (top field `L = E.field`, base field
`K = E.base`) such that `G_L` is normal in `G_K` (the hypothesis `hnormal`,
normality of `G_L` regarded as a subgroup of `G_K`). For `k ∈ G_K` and
`a ∈ A_L = ambientFixedAddSubgroup A E.field.field`, the action
`normalExtensionAction … hnormal k a = k · a ∈ A_L` does not change the
normalized valuation of `L`: `v_L(k · a) = v_L(a)` in the value group.
The hypothesis `hnormal` occurs in the proposition, as an argument of
`normalExtensionAction`, which needs it to show that `k · a` is again
`G_L`-fixed.

Binder names, order and kinds are those of the source theorem. The target
has no further hypothesis.

## Modification record

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the published names above.
2. Replace `theorem valuationAt_normalExtensionAction … : statement := proof`
   by `def valuationAt_normalExtensionActionStatement … : Prop := statement`.
   The statement is copied verbatim. The source proof is omitted: this
   contribution publishes a proposition target, and its proof is separate
   work.
3. Replace the source docstring by a description of the proposition that
   names the source theorem, and replace the source module docstring by a
   description of this module with a modification notice.
4. Replace the source imports of `Degree.PrimeElements` and
   `GaloisCohomology.Cyclic.TateComparison` by the focused imports
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Normalized.Definitions`,
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Definitions`
   and
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.Definitions`.
5. Retain both opens, the noncomputable section, the group-variable comment
   and both variable lines. Omit `open CategoryTheory` (line 28) and
   `universe u` (line 30), which the target does not use, and the whole
   `section Generic`. Omit all other source units. No helper declaration or
   instance is added.

This is the exact source statement as a named proposition, without a
published proof. It discharges no host class-formation, cup, transfer, Tate
or reciprocity target.

## Verification

The module passed a project Lean service check on 15 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), with no errors or warnings.
Declaration inspection reported `statement_returns_prop: true`, one universe
parameter and the axioms `propext`, `Classical.choice` and `Quot.sound`.
Compilation and inspection are separate from independent semantic acceptance
and publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
