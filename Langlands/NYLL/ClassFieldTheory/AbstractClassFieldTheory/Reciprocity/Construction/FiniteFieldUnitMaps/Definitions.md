# NYLL M045.001–M045.002: relative normality and finiteness across the residue-field enrichment

The paired Lean file adapts the two instances of Naganori
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

| Unit | Source instance after `ClassFormation.FiniteAbstractField.` | Docstring | Declaration | Adapted declaration |
| --- | --- | --- | --- | --- |
| M045.001 | `toFiniteResidueAbstractField_extensionNormal` | 37 | 38–44 | `Langlands.NYLL.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal` |
| M045.002 | `toFiniteResidueAbstractField_extensionFinite` | 46 | 47–56 | `Langlands.NYLL.ClassFormation.FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite` |

The enclosing source context is `universe u v` (line 19),
`namespace ClassFormation` (line 21), `open KummerTheory` and
`open CyclicCohomology` (lines 23–24), `noncomputable section` (line 28),
`open CategoryTheory` and `open scoped BigOperators` (lines 30–31) and the
variables `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`
(line 33). The instances are in `namespace FiniteAbstractField` (lines 35–58).
The rest of the source file (the `ValuationData` declarations, lines
60–246) is not part of this module; the statements of M045.007 and M045.010
are in the sibling module `Reciprocity.Construction.FiniteFieldUnitMaps.Statements`.

The names used resolve to `Langlands.NYLL` declarations:

- `IntegralRepGroupType` (M002.001), the abbreviation `Type 0`;
- `FiniteAbstractField` (M010.121), a field `K.field` finite over the
  distinguished base, and `DegreeData` (M010.002);
- `FiniteAbstractField.toFiniteResidueAbstractField` (M010.126, from
  `Degree.Fields.FiniteAbstractField.Residue.Definitions`), the
  enrichment of `K` to a `DegreeData.FiniteResidueAbstractField D` with the
  same field `K.field` (its finite residue quotient is derived from the
  finite relative quotient);
- `CyclicCohomology.extensionSubgroup` (M004.002), the abbreviation
  `L.toSubgroup.subgroupOf K.toSubgroup`.

`Subgroup.Normal`, `Finite` and quotient groups are Mathlib's.

## Instances

Both instances have the binders implicit `{G : IntegralRepGroupType}`,
`[Group G]` and `[TopologicalSpace G]`, followed by those shown.

### M045.001

```lean
instance toFiniteResidueAbstractField_extensionNormal
    (K : FiniteAbstractField G) (D : DegreeData G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal] :
    (extensionSubgroup (K.toFiniteResidueAbstractField D).field L hLK).Normal := by
  change (extensionSubgroup K.field L hLK).Normal
  exact hnormal
```

If `G_L` is normal in `G_K`, it is normal in the field of the residue
enrichment of `K`; the two subgroups agree definitionally, since
`(K.toFiniteResidueAbstractField D).field` is `K.field`.

### M045.002

```lean
instance toFiniteResidueAbstractField_extensionFinite
    (K : FiniteAbstractField G) (D : DegreeData G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    Finite ((K.toFiniteResidueAbstractField D).field.toSubgroup ⧸
      extensionSubgroup (K.toFiniteResidueAbstractField D).field L hLK) := by
  change Finite
    (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)
  exact hfinite
```

Likewise, finiteness of `G_K ⧸ G_L` transfers to the residue enrichment.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace the source imports by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Residue.Definitions`
   (M010.126, which also brings M010.002, M010.121 and M004.002) and
   `Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse` (M002.001).
3. Replace the source module docstring by a description of this module with
   a modification notice that names the source instances.
4. Omit the rest of the source file and the unused `universe u v`,
   `open KummerTheory`, `open CategoryTheory` and `open scoped BigOperators`.
   Retain `open CyclicCohomology` (for `extensionSubgroup`), the
   noncomputable section, the variable line and the namespace.
5. The binders, docstrings and bodies are unchanged. No helper declaration
   is added.

These instances discharge no host class-formation, cup, transfer, Tate or
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
