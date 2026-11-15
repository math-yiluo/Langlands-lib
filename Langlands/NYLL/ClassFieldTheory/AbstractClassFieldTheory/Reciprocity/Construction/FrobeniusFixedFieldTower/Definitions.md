# NYLL M041.001–M041.015: towers of Frobenius fixed fields

This file adapts fifteen declarations of Naganori Yamaguchi's
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean`
at pinned commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. The original file SHA-256 is
`3f556d66b84b17f410c3434db816784725dddab9b54a289d59166865174f14ca`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, with the
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The readable original is in the project's literature collection under
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

Original names have the prefix `ClassFormation.DegreeData.`, and adapted
names have the prefix `Langlands.NYLL.ClassFormation.DegreeData.`; the
table omits these prefixes.

| Unit | Kind | Source lines (docstring, declaration) | Name (original and adapted) |
| --- | --- | --- | --- |
| M041.001 | def | 30–31, 32–44 | `frobeniusFixedAbstractField` |
| M041.002 | structure | 46–52, 53–113 | `FrobeniusFixedFieldTower` |
| M041.003 | def | 119, 120–132 | `FrobeniusFixedFieldTower.base` |
| M041.004 | def | 134, 135–147 | `FrobeniusFixedFieldTower.field` |
| M041.005 | def | 149, 150–154 | `FrobeniusFixedFieldTower.toGaloisSubextension` |
| M041.006 | def | 156, 157–162 | `FrobeniusFixedFieldTower.extension` |
| M041.007 | structure | 164, 165–173 | `FrobeniusFixedFieldTower.Representative` |
| M041.008 | instance | 175, 176–179 | `FrobeniusFixedFieldTower.extensionNormal` |
| M041.009 | structure | 181, 182–190 | `FrobeniusFixedFieldTower.CyclicGenerator` |
| M041.010 | instance | 192, 193–198 | `FrobeniusFixedFieldTower.extensionFinite` |
| M041.011 | instance | 200, 201–210 | `FrobeniusFixedFieldTower.baseAbsoluteFiniteInstance` |
| M041.012 | instance | 212, 213–222 | `FrobeniusFixedFieldTower.fieldAbsoluteFiniteInstance` |
| M041.013 | structure | 226–228, 229–233 | `FiniteAmbientFrobeniusFixedFieldTower` |
| M041.014 | instance | 239–241, 242–245 | `FiniteAmbientFrobeniusFixedFieldTower.ambientQuotientFinite` |
| M041.015 | instance | 247–248, 249–256 | `FiniteAmbientFrobeniusFixedFieldTower.ambientRepresentedQuotientFinite` |

## The objects

Every object used is a source definition published in the Library, the
source definition M016.021 adapted in the sibling module of this
contribution, or a Mathlib definition.
No replacement field, Frobenius element, fixed field, extension or quotient
is introduced.

- `G : IntegralRepGroupType` (M002.001, the abbreviation
  `Langlands.NYLL.IntegralRepGroupType := Type 0`) is the ambient group, with
  `[Group G]` and `[TopologicalSpace G]`. Closed subgroups of `G`
  (Mathlib's `ClosedSubgroup G`) represent abstract fields, and a smaller
  subgroup is a larger field.
- `D : DegreeData G` (M010.002) is the source degree datum.
- `baseField G` (M010.003) is the distinguished base field, the closed
  subgroup `⊤`.
- `K : FiniteResidueAbstractField D` (M010.021) bundles a closed subgroup
  `K.field` with finiteness of its residue quotient.
- `GaloisSubextension K` (M010.052) for a closed subgroup `K` bundles a
  closed subgroup `field`, the inclusion `below : field.toSubgroup ≤ K.toSubgroup`
  and normality `normal` of `field.toSubgroup.subgroupOf K.toSubgroup` in
  `K.toSubgroup`. Its `extensionQuotient` (M010.054) is a named type equal by
  definition to `K.toSubgroup ⧸ field.toSubgroup.subgroupOf K.toSubgroup`,
  and `extensionQuotientMulEquiv` (M010.059) is the identity multiplicative
  equivalence between the two presentations.
- `D.FrobeniusElements K L hLK` (M012.009) is the type of Frobenius lifts
  `σ`, elements `σ.1` of the quotient
  `K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK` with strictly
  positive natural normalized degree.
- `D.frobeniusClosure K L hLK σ` (M014.023) is the closed subgroup
  `Γ = closure ⟨σ.1⟩` of
  `K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK`, and
  `D.frobeniusInClosure K L hLK σ` (M014.024) is `σ.1` regarded as an
  element of `Γ`. Both are published in the module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Definitions`.
- `D.frobeniusFixedField K L hLK σ` (M016.004) is the field fixed by `σ`, a
  closed subgroup of `G`. It is published in the module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.Definitions`.
- `D.frobeniusFixedFieldToClosure K L hLK σ` (M016.021) is the group
  homomorphism from the subgroup underlying
  `D.frobeniusFixedField K L hLK σ` to `D.frobeniusClosure K L hLK σ` that
  sends an element to its class modulo `D.extensionInertiaWithin K.field L hLK`.
  It is defined in the sibling module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.ToClosure.Definitions`
  of this contribution, which has its own Markdown.
- `FiniteAbstractField G` (M010.121) bundles a closed subgroup `field` with
  the finiteness `finite` of `(baseField G).toSubgroup ⧸ extensionSubgroup (baseField G) field (le_baseField field)`.
- `FiniteAbstractFieldExtension G` (M010.130) bundles two finite abstract
  fields `field` and `base`, the inclusion `below` of the underlying
  subgroups and the finiteness `finiteQuotient` of
  `base.field.toSubgroup ⧸ extensionSubgroup base.field field.field below`.
- `H.subgroupOf K` (Mathlib's `Subgroup.subgroupOf`) is the subgroup `H ⊓ K`
  of `K`, viewed as a subgroup of `K`. For closed subgroups `K` and `L` with
  `h : L.toSubgroup ≤ K.toSubgroup`, the source abbreviation
  `extensionSubgroup K L h` (M004.002, published as the abbreviation
  `Langlands.NYLL.CyclicCohomology.extensionSubgroup`) has the body
  `L.toSubgroup.subgroupOf K.toSubgroup` and does not use `h`.
- `Finite`, `Subgroup.Normal`, `Finite.of_equiv`, `QuotientGroup.mk` and
  `Subgroup.zpowers` (the subgroup of integer powers of an element) are
  Mathlib's.

## Telescopes

The source section variables are `{G : IntegralRepGroupType} [Group G]
[TopologicalSpace G]` (source line 26). Inside the namespaces
`FrobeniusFixedFieldTower` and `FiniteAmbientFrobeniusFixedFieldTower` the
section adds `{D : DegreeData G} [IsTopologicalGroup G]` (source lines 117
and 237). All are retained. No hypothesis is added or removed. In the
displayed binders, `extensionSubgroup` is expanded as described under
Modifications.

```lean
def frobeniusFixedAbstractField
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : DegreeData.FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK)
    [Finite ((baseField G).toSubgroup ⧸
      (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf
        (baseField G).toSubgroup)] :
    FiniteAbstractField G

structure FrobeniusFixedFieldTower (D : DegreeData G) [IsTopologicalGroup G]

def FrobeniusFixedFieldTower.base (T : FrobeniusFixedFieldTower D) :
    FiniteAbstractField G
def FrobeniusFixedFieldTower.field (T : FrobeniusFixedFieldTower D) :
    FiniteAbstractField G
def FrobeniusFixedFieldTower.toGaloisSubextension (T : FrobeniusFixedFieldTower D) :
    GaloisSubextension T.base.field
def FrobeniusFixedFieldTower.extension (T : FrobeniusFixedFieldTower D) :
    FiniteAbstractFieldExtension G
structure FrobeniusFixedFieldTower.Representative (T : FrobeniusFixedFieldTower D)
structure FrobeniusFixedFieldTower.CyclicGenerator (T : FrobeniusFixedFieldTower D)
    extends Representative T

structure FiniteAmbientFrobeniusFixedFieldTower
    (D : DegreeData G) [IsTopologicalGroup G]
    extends FrobeniusFixedFieldTower D
```

## The structures

`FrobeniusFixedFieldTower D` (M041.002) is a finite normal tower between two
Frobenius fixed fields of one ambient Galois extension. Write `Σ_b` and
`Σ_f` for `D.frobeniusFixedField ambientBase ambient.field ambient.below baseFrobenius`
and `D.frobeniusFixedField ambientBase ambient.field ambient.below fieldFrobenius`.
Its fields, in source order, are:

- `ambientBase : FiniteResidueAbstractField D`, the finite-residue field in
  which the ambient Galois extension begins;
- `ambient : GaloisSubextension ambientBase.field`, the ambient Galois
  extension;
- `baseFrobenius` and `fieldFrobenius`, two Frobenius lifts in
  `D.FrobeniusElements ambientBase ambient.field ambient.below`, whose fixed
  fields are the bottom `Σ_b` and the top `Σ_f` of the tower;
- `field_le_base : Σ_f.toSubgroup ≤ Σ_b.toSubgroup`, the inclusion of the top
  fixed field in the bottom one (as subgroups the inclusion is reversed);
- `finiteQuotient : Finite (Σ_b.toSubgroup ⧸ Σ_f.toSubgroup.subgroupOf Σ_b.toSubgroup)`,
  finiteness of the relative Galois quotient;
- `baseAbsoluteFinite` and `fieldAbsoluteFinite`: finiteness of
  `(baseField G).toSubgroup ⧸ Σ.toSubgroup.subgroupOf (baseField G).toSubgroup`
  for `Σ = Σ_b` and `Σ = Σ_f`, so that both fixed fields are finite over the
  distinguished base;
- `normal : (Σ_f.toSubgroup.subgroupOf Σ_b.toSubgroup).Normal`, normality of
  the relative subgroup;
- `commute : baseFrobenius.1 * fieldFrobenius.1 = fieldFrobenius.1 * baseFrobenius.1`,
  commutation of the two Frobenius lifts in the ambient quotient.

The structure stores only data and hypotheses and asserts no property of the
fixed fields beyond its own fields.

For `T : FrobeniusFixedFieldTower D`, `T.Representative` (M041.007) has
two fields:

- `element : T.extension.base.field.toSubgroup`, an element of the subgroup
  underlying the bottom fixed field `Σ_b`;
- `mapsToFrobenius`, the equation
  `D.frobeniusFixedFieldToClosure T.ambientBase T.ambient.field T.ambient.below T.baseFrobenius element = D.frobeniusInClosure T.ambientBase T.ambient.field T.ambient.below T.baseFrobenius`:
  the class of `element` modulo the inertia subgroup is the Frobenius lift
  `T.baseFrobenius`, as an element of its closure.

Here `T.extension.base.field` reduces by definition to `Σ_b`, so `element`
has the domain type of `D.frobeniusFixedFieldToClosure`.

`T.CyclicGenerator` (M041.009) extends `T.Representative` by the single
field `generates`: every `x` in
`T.extension.base.field.toSubgroup ⧸ T.extension.field.field.toSubgroup.subgroupOf T.extension.base.field.toSubgroup`
lies in `Subgroup.zpowers (QuotientGroup.mk toRepresentative.element)`, that
is, the class of the representative generates the relative Galois quotient
of the tower. The structure asserts only its fields; it does not assert that
such a representative or generator exists.

`FiniteAmbientFrobeniusFixedFieldTower D` (M041.013) extends
`FrobeniusFixedFieldTower D` by the single field
`ambientFinite : Finite toFrobeniusFixedFieldTower.ambient.extensionQuotient`,
finiteness of the ambient Galois quotient.

## Constructions

- `D.frobeniusFixedAbstractField K L hLK σ` (M041.001) bundles the fixed
  field `D.frobeniusFixedField K L hLK σ` with the instance hypothesis that it
  is finite over the distinguished base, as a `FiniteAbstractField G`: its
  `field` is the fixed field and its `finite` is found by `inferInstance`
  from that hypothesis. The body is the source's.
- `T.base` (M041.003) and `T.field` (M041.004) are
  `D.frobeniusFixedAbstractField T.ambientBase T.ambient.field T.ambient.below σ`
  for `σ = T.baseFrobenius` and `σ = T.fieldFrobenius`. Each body first
  installs `T.baseAbsoluteFinite`, respectively `T.fieldAbsoluteFinite`, as a
  local instance with `letI`, as in the source.
- `T.toGaloisSubextension` (M041.005) is the Galois subextension of
  `T.base.field` with `field := T.field.field`, `below := T.field_le_base`
  and `normal := T.normal`.
- `T.extension` (M041.006) is the finite extension with `field := T.field`,
  `base := T.base`, `below := T.field_le_base` and
  `finiteQuotient := T.finiteQuotient`.

The fields of `T.base` and `T.field` reduce by definition to `Σ_b` and
`Σ_f`, so the fields of `T` have the types that these constructions require.

## Instances

All instance bodies are the source's single field projections.

- M041.008 `extensionNormal`:
  `(T.extension.field.field.toSubgroup.subgroupOf T.extension.base.field.toSubgroup).Normal`,
  given by `T.normal`.
- M041.010 `extensionFinite`:
  `Finite (T.extension.base.field.toSubgroup ⧸ T.extension.field.field.toSubgroup.subgroupOf T.extension.base.field.toSubgroup)`,
  given by `T.finiteQuotient`.
- M041.011 `baseAbsoluteFiniteInstance` and M041.012
  `fieldAbsoluteFiniteInstance`: finiteness of `Σ_b` and `Σ_f` over the
  distinguished base, given by `T.baseAbsoluteFinite` and
  `T.fieldAbsoluteFinite`.
- M041.014 `ambientQuotientFinite`: `Finite T.ambient.extensionQuotient` for
  `T : FiniteAmbientFrobeniusFixedFieldTower D`, given by `T.ambientFinite`.
- M041.015 `ambientRepresentedQuotientFinite`:
  `Finite (T.ambientBase.field.toSubgroup ⧸ T.ambient.field.toSubgroup.subgroupOf T.ambientBase.field.toSubgroup)`,
  given by `Finite.of_equiv T.ambient.extensionQuotient T.ambient.extensionQuotientMulEquiv`.

## Modifications

Worker 5264 makes these modifications:

- Extract only the fifteen declarations in the table, with the namespaces
  `ClassFormation` (line 18), `DegreeData` (line 28),
  `FrobeniusFixedFieldTower` (line 115) and
  `FiniteAmbientFrobeniusFixedFieldTower` (line 235), the noncomputable
  section (line 24) and the variable declarations (lines 26, 117 and 237).
  Replace the module documentation by one describing these declarations and
  the modifications.
- Prefix the source namespace `ClassFormation` with `Langlands.NYLL`.
- Expand every occurrence of the source abbreviation
  `extensionSubgroup K L h` to its exact body
  `L.toSubgroup.subgroupOf K.toSubgroup`, following the published sibling
  modules. The occurrences are in the binders of M041.001 (lines 36 and
  39–41), the fields `finiteQuotient`, `baseAbsoluteFinite`,
  `fieldAbsoluteFinite` and `normal` of M041.002 (lines 76–81, 86–91,
  96–101 and 104–109), the local instances of M041.003 and M041.004 (lines
  124–129 and 139–144), the field `generates` of M041.009 (lines 187–189)
  and the instance types of M041.008, M041.010, M041.011, M041.012 and
  M041.015. The two expressions are definitionally
  equal. The expansion drops the unused proof arguments
  `le_baseField (...)`, `field_le_base`, `T.extension.below` and
  `T.ambient.below` of `extensionSubgroup`, so the theorem `le_baseField`
  (M010.005) is no longer used.
- Omit the unused source `universe u` (line 16), `open KummerTheory`
  (line 20) and `open CyclicCohomology` (line 22). The latter served only to
  resolve `extensionSubgroup`.
- Replace the source imports `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusPowerFixedField`
  and `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension`
  by the sibling module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.ToClosure.Definitions`
  of this contribution (M016.021 and, transitively through the published
  FrobeniusField and FrobeniusClosure definitions modules, M016.004,
  M014.023, M014.024, M010.002, M010.003, M010.021 and M012.009) and the
  published modules
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.Definitions`
  (M010.121, M010.130),
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.GaloisSubextension.Definitions`
  (M010.052, M010.054, M010.059) and
  `Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse` (M002.001).
- The declaration names, docstrings, the remaining telescopes and result
  types, the structure fields and the construction and instance bodies are
  unchanged.
- Retain the original copyright, Apache-2.0 and author header, and add the
  explicit modification record in the Lean module documentation.

The later declarations of the source file, from M041.016
`FrobeniusPowerFixedFieldTower` (docstring line 260) on, are not part of this
contribution. These definitions discharge no host class-formation, cup,
transfer, Tate or reciprocity target.

## Verification

The module and its sibling ToClosure module passed a project Lean service check on 15 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), with no errors or warnings.
Compilation is separate from independent semantic acceptance and
publication.

## Attribution

The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
