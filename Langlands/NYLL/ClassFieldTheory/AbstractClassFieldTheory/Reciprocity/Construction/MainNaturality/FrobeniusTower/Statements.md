# NYLL M066.006: the Frobenius tower map multiplies normalized degree by `f`

The paired Lean file adapts the statement of the theorem `finiteReciprocityNaturalityFrobeniusTowerMap_degree` of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainNaturality.lean`.
The pinned source file has SHA-256
`0107befcff3ba066d7663120d9aa823ae72911cef7d3e72c5eeb5cb95f73a533`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.DegreeData.` | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M066.006 | `finiteReciprocityNaturalityFrobeniusTowerMap_degree` | 142–143 | 144–160 | 160–165 | `Langlands.NYLL.ClassFormation.DegreeData.finiteReciprocityNaturalityFrobeniusTowerMap_degreeStatement` |

The enclosing source context is `universe u` (line 19),
`namespace ClassFormation` (line 21), `open KummerTheory` (line 23),
`open CyclicCohomology` (line 25), `open CategoryTheory` (line 27),
`noncomputable section` (line 32), `open scoped BigOperators` (line 34),
`section GroupOnly` (lines 36–415), the variables
`{G : Type u} [Group G] [TopologicalSpace G]` (line 38) and
`namespace DegreeData` (lines 78–401). The source import (line 7) is the
unported module
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainFiniteReciprocity`.
The rest of the source file is not part of this module; the definition
M066.003 used here is already published in the sibling module
`Reciprocity.Construction.MainNaturality.FrobeniusTower.Definitions`.

The names used resolve to `Langlands.NYLL` declarations:

- `DegreeData` (M010.002) and `DegreeData.FiniteResidueAbstractField D`
  (M010.021), with the projection `FiniteResidueAbstractField.toSubgroup`
  (M010.023) of `K` to the subgroup `K.field.toSubgroup`;
- `DegreeData.FiniteResidueAbstractExtension D` (M010.111, from
  `Degree.Fields.FiniteResidueExtension.Definitions`), a pair of finite-residue
  abstract fields `E.field` and `E.base` with
  `E.below : E.field.field.toSubgroup ≤ E.base.field.toSubgroup` and a
  finite relative quotient, and its residue degree
  `FiniteResidueAbstractExtension.residueDegree` (M010.116, from
  `Degree.Fields.FiniteResidueExtension.ResidueDegreeDefinitions`), a
  positive natural number `f = f(E.field | E.base)`;
- `DegreeData.extensionInertiaWithin` (M012.002), the subgroup `G_L ⊓ I_K`
  of `G_K`, and `DegreeData.extensionNormalizedDegree` (M012.005, from
  `Degree.FrobeniusLift.FrobeniusElements.Definitions`), the normalized
  degree `G_K ⧸ (G_L ⊓ I_K) →* ZHatMul`, where `ZHatMul` (M010.001) is
  `Multiplicative ZHat`;
- `DegreeData.finiteReciprocityNaturalityFrobeniusTowerMap` (M066.003,
  from `Reciprocity.Construction.MainNaturality.FrobeniusTower.Definitions`):
  for `G_{L'} ≤ G_{K'} ≤ G_K`, `G_{L'} ≤ G_L ≤ G_K`, the monoid homomorphism
  `G_{K'} ⧸ (G_{L'} ⊓ I_{K'}) →* G_K ⧸ (G_L ⊓ I_K)` induced by the inclusion
  `G_{K'} ≤ G_K`;
- `CyclicCohomology.extensionSubgroup` (M004.002), the abbreviation
  `L.toSubgroup.subgroupOf K.toSubgroup`.

`ZHat` (M008.008, from
`GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Definitions`) is
the profinite integers with their additive group structure.
`IsTopologicalGroup`, `Multiplicative.toAdd`, the coercion `ℕ+ → ℕ` and
`nsmul` are Mathlib's.

## Target and complete telescope

The target has the binders implicit `{G : Type u}`, `[Group G]` and
`[TopologicalSpace G]`, followed by:

```lean
def finiteReciprocityNaturalityFrobeniusTowerMap_degreeStatement
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.FiniteResidueAbstractExtension D)
    (L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ E.base.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ E.field.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup E.base.field L hLK).Normal]
    [hL'normal : (extensionSubgroup E.field.field L' hL'K').Normal]
    (q : E.field.toSubgroup ⧸
      D.extensionInertiaWithin E.field.field L' hL'K') : Prop :=
    (D.extensionNormalizedDegree E.base L hLK
      (D.finiteReciprocityNaturalityFrobeniusTowerMap
        E.base.field E.field.field L L'
        hLK hL'K' E.below hL'L q)).toAdd =
      (E.residueDegree : ℕ) •
        (D.extensionNormalizedDegree E.field L' hL'K' q).toAdd
```

Write `K = E.base` and `K' = E.field`, a finite extension of `K` with
residue degree `f`, and let `L | K` and `L' | K'` be Galois with
`G_{L'} ≤ G_L`. For every `q ∈ G_{K'} ⧸ (G_{L'} ⊓ I_{K'})`, the
normalized degree over `K` of the image of `q` under the tower map equals
`f` times the normalized degree of `q` over `K'` (both read additively in
`ZHat`).

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace `theorem finiteReciprocityNaturalityFrobeniusTowerMap_degree … : statement := proof`
   by `def finiteReciprocityNaturalityFrobeniusTowerMap_degreeStatement … : Prop := statement`.
   The statement is copied verbatim. The source proof is omitted: this
   contribution publishes the proposition target, and its proof is separate
   work.
3. Prefix the source docstring with `Target:`. Replace the source module
   docstring by a description of this module with a modification notice
   that names the source theorem.
4. Replace the source import by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainNaturality.FrobeniusTower.Definitions`
   (M066.003, which also brings M010.002 and M012.002),
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.FrobeniusElements.Definitions`
   (M012.005, which also brings M010.001, M010.021 and M010.023),
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidueExtension.ResidueDegreeDefinitions`
   (M010.116, which also brings M010.111) and
   `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`
   (M004.002).
5. Omit the other declarations of the source file, the section `GroupOnly`
   (its variable line is kept) and the unused `open KummerTheory`,
   `open CategoryTheory` and `open scoped BigOperators`. Retain the universe,
   `open CyclicCohomology`, the noncomputable section and the namespaces.
6. No helper declaration or instance is added.

This is an exact source statement as a named proposition, without a
published proof. It discharges no host class-formation, cup, transfer, Tate
or reciprocity target.

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
