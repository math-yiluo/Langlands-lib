# NYLL M049.001–M049.002: the finite-field extension bundle of a finite intermediate field

The paired Lean file adapts the first two definitions of Naganori
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

| Unit | Source definition after `ClassFormation.FiniteIntermediateField.` | Docstring | Declaration | Adapted declaration |
| --- | --- | --- | --- | --- |
| M049.001 | `toFiniteAbstractFieldExtension` | 36–37 | 38–45 | `Langlands.NYLL.ClassFormation.FiniteIntermediateField.toFiniteAbstractFieldExtension` |
| M049.002 | `toFiniteAbstractField` | 47 | 48–51 | `Langlands.NYLL.ClassFormation.FiniteIntermediateField.toFiniteAbstractField` |

The enclosing source context is `universe u v` (line 18),
`namespace ClassFormation` (line 20), `open KummerTheory` and
`open CyclicCohomology` (lines 22–23), `noncomputable section` (line 27),
`open CategoryTheory` and `open scoped BigOperators` (lines 29–30), the
variables `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`
(line 32) and `namespace FiniteIntermediateField` (lines 34–53). The rest of
the source file (lines 55–509, the `ValuationData` declarations from
M049.003 on) is not part of this module.

The names used resolve to `Langlands.NYLL` declarations:

- `IntegralRepGroupType` (M002.001, from
  `GaloisCohomology.Cyclic.IntegralRepUniverse`), the abbreviation `Type 0`;
- `FiniteIntermediateField E K` (M029.001, from
  `Reciprocity.Construction.NormSubgroup.Definitions`), a closed subgroup
  `M.field` with `M.above : E.toSubgroup ≤ M.field.toSubgroup`,
  `M.below : M.field.toSubgroup ≤ K.toSubgroup` and
  `M.finite : Finite (K.toSubgroup ⧸ extensionSubgroup K M.field M.below)`;
- `FiniteAbstractField` (M010.121, from
  `Degree.Fields.FiniteAbstractField.Definitions`), a field `K.field`
  finite over the distinguished base;
- `FiniteAbstractFieldExtension` (M010.130, from
  `Degree.Fields.FiniteAbstractField.Extension.Definitions`), a pair of
  finite abstract fields `field ≤ base` with a finite relative quotient;
- `FiniteAbstractFieldExtension.ofInclusion` (M010.131, from
  `Degree.Fields.FiniteAbstractField.Extension.OfInclusion`), which bundles a
  closed subgroup `field` below a finite abstract field `base`, given an
  instance that the relative quotient is finite, as a finite abstract field
  extension with that top `field` and that `base`;
- `CyclicCohomology.extensionSubgroup` (M004.002), the abbreviation
  `L.toSubgroup.subgroupOf K.toSubgroup`.

## Definitions

Both definitions have the binders implicit `{G : IntegralRepGroupType}`,
`[Group G]` and `[TopologicalSpace G]`, followed by those shown.

### M049.001

```lean
noncomputable def toFiniteAbstractFieldExtension
    {E : ClosedSubgroup G} (K : FiniteAbstractField G)
    (M : FiniteIntermediateField E K.field) :
    FiniteAbstractFieldExtension G := by
  letI : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field M.field M.below) :=
    M.finite
  exact FiniteAbstractFieldExtension.ofInclusion M.field K M.below
```

For a finite abstract field `K` and a finite intermediate field `M` of an
extension `E | K.field`, the finite abstract field extension with base `K`
and top field `M.field`, built by `ofInclusion` from the finiteness field
`M.finite`.

### M049.002

```lean
noncomputable def toFiniteAbstractField
    {E : ClosedSubgroup G} (K : FiniteAbstractField G)
    (M : FiniteIntermediateField E K.field) : FiniteAbstractField G :=
  (M.toFiniteAbstractFieldExtension K).field
```

The top field of that extension: `M` regarded as a finite abstract field.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace the source imports by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Definitions`
   (M029.001, which also brings M004.002),
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.OfInclusion`
   (M010.131, which also brings M010.121 and M010.130) and
   `Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse` (M002.001).
3. Replace the source module docstring by a description of this module with
   a modification notice that names the source definitions.
4. Omit the rest of the source file and the unused `universe u v`,
   `open KummerTheory`, `open CategoryTheory` and `open scoped BigOperators`.
   Retain `open CyclicCohomology` (for `extensionSubgroup`), the
   noncomputable section, the variable line and the namespaces.
5. The binders, docstrings, `noncomputable` modifiers and bodies are
   unchanged. No helper declaration or instance is added.

These definitions discharge no host class-formation, cup, transfer, Tate or
reciprocity target.

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
