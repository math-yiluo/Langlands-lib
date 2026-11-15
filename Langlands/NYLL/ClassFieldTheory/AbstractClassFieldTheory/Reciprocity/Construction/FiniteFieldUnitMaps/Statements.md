# NYLL M045.007 and M045.010: unit groups are preserved by inclusion and relative norm

The paired Lean file adapts the statements of the theorems `fixedFieldInclusion_mem_unitAddSubgroup` and `relativeNorm_mem_unitAddSubgroup` of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteFieldUnitMaps.lean`.
The pinned source file has SHA-256
`7c304aaabeb8f4e08738e1d7e727db097444cf7d1cc011e1be6662cea5ba44fe`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.ValuationData.` | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M045.007 | `fixedFieldInclusion_mem_unitAddSubgroup` | 158–160 | 161–165 | 165–195 | `Langlands.NYLL.ClassFormation.ValuationData.fixedFieldInclusion_mem_unitAddSubgroupStatement` |
| M045.010 | `relativeNorm_mem_unitAddSubgroup` | 217–219 | 220–224 | 224–235 | `Langlands.NYLL.ClassFormation.ValuationData.relativeNorm_mem_unitAddSubgroupStatement` |

The enclosing source context is `universe u v` (line 19),
`namespace ClassFormation` (line 21), `open KummerTheory` and
`open CyclicCohomology` (lines 23–24), `noncomputable section` (line 28),
`open CategoryTheory` and `open scoped BigOperators` (lines 30–31) and the
variables `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`
(line 33). The theorems are in `namespace ValuationData` (lines 60–246),
after `variable {D : DegreeData G} {A : Rep ℤ G}` (line 62). The other
declarations of the source file are not part of this module; the instances
M045.001–M045.002 are in the sibling module
`Reciprocity.Construction.FiniteFieldUnitMaps.Definitions`.

The names used in the statements resolve to `Langlands.NYLL` declarations:

- `IntegralRepGroupType` (M002.001), `DegreeData` (M010.002) and
  `ValuationData D A` (M025.012), valuation data for the representation
  `A`, with the normalized valuation `ValuationData.valuationAt` (M025.025)
  `v.valuationAt K : ambientFixedAddSubgroup A K.field →+ v.valueGroup`;
- `FiniteAbstractFieldExtension` (M010.130, from
  `Degree.Fields.FiniteAbstractField.Extension.Definitions`), finite
  abstract fields `E.field` (top) and `E.base` with
  `E.below : E.field.field.toSubgroup ≤ E.base.field.toSubgroup` and a
  finite relative quotient, supplied as an instance by the anonymous source
  instance M010.139 (published as
  `Langlands.NYLL.PortInternal.M010.d139` in the same module);
- `ValuationData.unitAddSubgroup` (M028.008, from
  `Degree.PrimeElements.Prime.Definitions`), the additive unit group
  `U_K = ker v_K` inside `A_K = ambientFixedAddSubgroup A K.field`;
- `fixedFieldInclusion` (M028.001, from `Degree.PrimeElements.Definitions`),
  the inclusion `A_K →+ A_L` for `G_L ≤ G_K`;
- `relativeNorm` (M024.009, from `Degree.Norm.RelativeNorm.Definitions`),
  the relative norm `A_L →+ A_K` for `G_L ≤ G_K` with finite
  `G_K ⧸ G_L` (an instance argument, found from M010.139).

## Targets and complete telescopes

Both targets have the binders implicit `{G : IntegralRepGroupType}`,
`[Group G]`, `[TopologicalSpace G]`, `{D : DegreeData G}` and
`{A : Rep ℤ G}`, followed by those shown.

### M045.007

```lean
def fixedFieldInclusion_mem_unitAddSubgroupStatement
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (u : v.unitAddSubgroup E.base) : Prop :=
    fixedFieldInclusion A E.base.field E.field.field E.below u.1 ∈
      v.unitAddSubgroup E.field
```

For a finite extension `E` with top field `L = E.field` and base
`K = E.base`, the inclusion `A_K → A_L` maps each unit `u ∈ U_K` into
`U_L`.

### M045.010

```lean
def relativeNorm_mem_unitAddSubgroupStatement
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (u : v.unitAddSubgroup E.field) : Prop :=
    relativeNorm A E.base.field E.field.field E.below u.1 ∈
      v.unitAddSubgroup E.base
```

In the same setting, the relative norm `N_{L|K} : A_L → A_K` maps each
unit `u ∈ U_L` into `U_K`.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. The statements are copied
   verbatim. The source proofs are omitted: this contribution publishes
   proposition targets, and their proofs are separate work.
3. Prefix both source docstrings with `Target:`, keeping the rest of their
   text. Replace the source module docstring by a description of this
   module with a modification notice that names the source theorems.
4. Replace the source imports by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Prime.Definitions`
   (M028.008, which also brings M025.012, M025.025 and M010.121),
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Definitions`
   (M028.001),
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions`
   (M024.009) and
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.Definitions`
   (M010.130, M010.139).
5. Omit the other declarations of the source file and the unused
   `universe u v`, `open KummerTheory`, `open CyclicCohomology`,
   `open CategoryTheory` and `open scoped BigOperators`. Retain the
   noncomputable section, both variable lines and the namespace.
6. No helper declaration or instance is added.

These are exact source statements as named propositions, without
published proofs. They discharge no host class-formation, cup, transfer,
Tate or reciprocity target.

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
