# NYLL M049.004: finite-stage units of an infinite extension

The paired Lean file adapts the definition `ValuationData.IsFiniteStageUnit` of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/InfiniteUnitDescent.lean`.
The pinned source file has SHA-256
`fb8faf0a2a0443ef5c0a5f73b334008c2a045923c98a1d7424bd6f4b54994957`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source definition after `ClassFormation.ValuationData.` | Docstring | Declaration | Adapted declaration |
| --- | --- | --- | --- | --- |
| M049.004 | `IsFiniteStageUnit` | 141–143 | 144–150 | `Langlands.NYLL.ClassFormation.ValuationData.IsFiniteStageUnit` |

The enclosing source context is `universe u v` (line 18),
`namespace ClassFormation` (line 20), `open KummerTheory` (line 22),
`open CyclicCohomology` (line 23), `noncomputable section` (line 27),
`open CategoryTheory` (line 29), `open scoped BigOperators` (line 30), the
variables `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`
(line 32), `namespace ValuationData` (line 55) and the variables
`{D : DegreeData G} {A : Rep ℤ G}` (line 57). The source imports (lines
7–8) are the unported modules `FixedTowerUnitDescent` and
`FiniteFieldUnitMaps` of
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction`.
The definitions M049.001 and M049.002 of the same source file are published
in `Reciprocity.Construction.InfiniteUnitDescent.Definitions`; the rest of
the source file is not part of this module.

The names used resolve to `Langlands.NYLL` declarations:

- `IntegralRepGroupType` (M002.001, from
  `GaloisCohomology.Cyclic.IntegralRepUniverse`), the abbreviation `Type 0`;
- `DegreeData G` (M010.002, from `Degree.Fields.Definitions`), a continuous
  surjective degree homomorphism `G →ₜ* ZHatMul`;
- `ValuationData D A` (M025.012, from
  `Degree.Valuation.ValuationData.Definitions`), a henselian valuation of the
  base-field fixed module;
- `FiniteAbstractField G` (M010.121, from
  `Degree.Fields.FiniteAbstractField.Definitions`), a closed subgroup
  `K.field` of finite index over the base field;
- `KummerTheory.ambientFixedAddSubgroup A H` (M023.001, from
  `GaloisCohomology.Kummer.Abstract.KummerDelta.U001.Definitions`), the
  additive subgroup `A^H` of elements of `A` fixed by `H`;
- `FiniteIntermediateField E K` (M029.001, from
  `Reciprocity.Construction.NormSubgroup.Definitions`), a closed subgroup
  `M.field` with `M.above : E.toSubgroup ≤ M.field.toSubgroup`,
  `M.below : M.field.toSubgroup ≤ K.toSubgroup` and the finiteness `M.finite`
  of `K.toSubgroup ⧸ extensionSubgroup K M.field M.below`, an intermediate
  field `E | M | K` finite over `K`;
- `FiniteIntermediateField.toFiniteAbstractField K M` (M049.002, from
  `Reciprocity.Construction.InfiniteUnitDescent.Definitions`), `M` as a
  finite abstract field: the upper endpoint of
  `FiniteAbstractFieldExtension.ofInclusion M.field K M.below`, whose field
  is `M.field`;
- `ValuationData.unitAddSubgroup v K` (M028.008, from
  `Degree.PrimeElements.Prime.Definitions`), the kernel `U_K` of the
  normalized valuation `v_K` (M025.025) on `A^{G_K}`;
- `fixedFieldInclusion A K L hLK` (M028.001, from
  `Degree.PrimeElements.Definitions`), the inclusion `A^{G_K} →+ A^{G_L}`
  for `G_L ≤ G_K`.

`ClosedSubgroup` and `Rep ℤ G` are Mathlib's.

## Definition

The definition has the binders implicit `{G : IntegralRepGroupType}`,
`[Group G]`, `[TopologicalSpace G]`, `{D : DegreeData G}` and
`{A : Rep ℤ G}`, followed by:

```lean
def IsFiniteStageUnit
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A E) : Prop :=
  ∃ M : FiniteIntermediateField E K.field,
    ∃ u : v.unitAddSubgroup (M.toFiniteAbstractField K),
      fixedFieldInclusion A M.field E M.above u.1 = a
```

For a closed subgroup `E` (an extension, possibly infinite, of the finite
field `K`), an element `a ∈ A^{G_E}` is a finite-stage unit when, for some
finite intermediate field `M` of `E | K`, it is the image under the
inclusion `A^{G_M} → A^{G_E}` of a unit `u ∈ U_M`. It is a proposition.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace the source imports by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.InfiniteUnitDescent.Definitions`
   (M049.002, which also brings M029.001, M010.121 and M002.001),
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Prime.Definitions`
   (M028.008, which also brings M025.012, M010.002 and M023.001) and
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Definitions`
   (M028.001).
3. Replace the source module docstring by a description of this module with
   a modification notice that names the source definition.
4. Omit the rest of the source file, the unused `universe u v` and the
   unused `open CyclicCohomology`, `open CategoryTheory` and
   `open scoped BigOperators`. Retain `open KummerTheory` (for
   `ambientFixedAddSubgroup`), the noncomputable section, both variable lines
   and the namespaces.
5. The binders, docstring and body are unchanged.

No helper declaration or instance is added. This definition discharges
no host class-formation, cup, transfer, Tate or reciprocity target.

## Verification

The module passed a project Lean service check on 15 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), with no errors or warnings.
Compilation is separate from independent semantic acceptance and
publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
