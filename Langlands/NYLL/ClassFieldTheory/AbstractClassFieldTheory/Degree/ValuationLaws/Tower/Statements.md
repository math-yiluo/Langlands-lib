# NYLL M027.007: the norm–valuation formula for a finite tower

The paired Lean file adapts the statement of one theorem from Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/ValuationLaws.lean`.
The pinned source file has SHA-256
`f540072f238d978f402034f3404bdaca624ff649cddf81e41cd8b9c7f73b68f8`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M027.007 | `ClassFormation.ValuationData.normalizedValuation_tower` | 164–165 | 166–172 | 173–202 | `Langlands.NYLL.ClassFormation.ValuationData.normalizedValuation_towerStatement` |

The enclosing source context is `namespace ClassFormation` (line 17),
`open KummerTheory` (line 19), `open CyclicCohomology` (line 21),
`noncomputable section` (line 25), the comment and variables at lines 27–29,
and `namespace ValuationData` (line 114).

The names used in the statement resolve to published `Langlands.NYLL`
declarations: `ClassFormation.ValuationData` (M025.012),
`ClassFormation.ValuationData.valueGroup` (M025.013) and
`ClassFormation.ValuationData.valuationAt` (M025.025, in
`Degree.Valuation.ValuationData.Normalized.Definitions`),
`ClassFormation.FiniteAbstractFieldExtension` (M010.130) with its fields
`field`, `base` and `below`,
`ClassFormation.FiniteAbstractFieldExtension.toFiniteResidueAbstractExtension`
(M010.140, in `Degree.Fields.FiniteAbstractField.Residue.Definitions`),
`ClassFormation.DegreeData.FiniteResidueAbstractExtension.residueDegree`
(M010.116, in `Degree.Fields.FiniteResidueExtension.ResidueDegreeDefinitions`),
`ClassFormation.relativeNorm` (M024.009, in
`Degree.Norm.RelativeNorm.Definitions`), whose `Finite` quotient argument is
supplied by the published instance `PortInternal.M010.d139` (M010.139),
`ClassFormation.DegreeData` (M010.002), `ZHat` (M008.008),
`KummerTheory.ambientFixedAddSubgroup` (M023.001) and
`IntegralRepGroupType` (M002.001). The coercions from `ℕ+` to `ℕ` and from
the value group to `ZHat`, the `ℕ`-scalar action on `ZHat`, `let` and `Rep`
are Lean's or Mathlib's.

## Target and complete telescope

The target has the section binders implicit
`{G : Langlands.NYLL.IntegralRepGroupType}`, `[Group G]`,
`[TopologicalSpace G]`, `{D : DegreeData G}` and `{A : Rep ℤ G}`, followed by
the explicit binders shown. The group lies in `Type 0`; the carrier of `A`
has an arbitrary universe, the single universe parameter.

```lean
def normalizedValuation_towerStatement (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (a : ambientFixedAddSubgroup A E.field.field) : Prop :=
    let ER := E.toFiniteResidueAbstractExtension D
    (ER.residueDegree : ℕ) •
        ((v.valuationAt E.field a : v.valueGroup) : ZHat) =
      ((v.valuationAt E.base
        (relativeNorm A E.base.field E.field.field E.below a) : v.valueGroup) : ZHat)
```

For a finite tower `L | K` given by `E` (top field `L = E.field`, base field
`K = E.base`) and `a ∈ A_L = ambientFixedAddSubgroup A E.field.field`, write
`f_{L|K} = (ER.residueDegree : ℕ)` for the relative residue degree of the
residue extension `ER` attached to `E` and `D`. The proposition is
`f_{L|K} · v_L(a) = v_K(N_{L|K} a)` in `ZHat`, where `v_L` and `v_K` are the
normalized valuations `v.valuationAt E.field` and `v.valuationAt E.base`,
coerced from the value group `Z` to `ZHat`, and `N_{L|K}` is
`relativeNorm A E.base.field E.field.field E.below`. This is the source's
norm–valuation formula `v_K ∘ N_{L|K} = f_{L|K} v_L`. The local `let` is part
of the source statement and is kept.

Binder names, order and kinds are those of the source theorem. The target
has no further hypothesis.

## Modification record

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the published names above.
2. Replace `theorem normalizedValuation_tower … : statement := proof` by
   `def normalizedValuation_towerStatement … : Prop := statement`. The
   statement, including its `let`, is copied verbatim. The source proof is
   omitted: this contribution publishes a proposition target, and its proof
   is separate work.
3. Replace the source docstring by a description of the proposition that
   names the source theorem and keeps its title, and replace the source
   module docstring by a description of this module with a modification
   notice.
4. Replace the source imports of `Degree.Valuation` and `Degree.NormLaws` by
   the focused imports
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Normalized.Definitions`,
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Residue.Definitions`,
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidueExtension.ResidueDegreeDefinitions`
   and
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions`.
5. Retain both opens, the noncomputable section, the group-variable comment
   and both variable lines. Omit all other source units. No helper
   declaration or instance is added.

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
