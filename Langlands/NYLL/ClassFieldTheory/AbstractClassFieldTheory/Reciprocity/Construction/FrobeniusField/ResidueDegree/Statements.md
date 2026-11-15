# NYLL M016.015 and M016.018: targets about the degree image of the Frobenius fixed field

The paired Lean file adapts the statements of two theorems from Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean`.
The pinned source file has SHA-256
`707b3783859e0c991b0a4e5a3a5c014c808617f79587d1895e49787a26d1ca10`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.DegreeData.` | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M016.015 | `frobeniusFixedSubgroupWithin_normalizedDegree_image` | 324–325 | 326–334 | 335–353 | `Langlands.NYLL.ClassFormation.DegreeData.frobeniusFixedSubgroupWithin_normalizedDegree_imageStatement` |
| M016.018 | `frobeniusFixedField_relativeResidueQuotientFinite` | 438–440 | 441–452 | 453–458 | `Langlands.NYLL.ClassFormation.DegreeData.frobeniusFixedField_relativeResidueQuotientFiniteStatement` |

The enclosing source context is `namespace ClassFormation` (line 17),
`open CyclicCohomology` (line 19), `noncomputable section` (line 23), the
variables at line 25 and `namespace DegreeData` (line 27). The source file
has no universe declaration.

The names used in the statements resolve to `Langlands.NYLL` declarations:
`DegreeData.frobeniusFixedSubgroupWithin` and `DegreeData.frobeniusFixedField`
(M016.001 and M016.004, from
`Reciprocity.Construction.FrobeniusField.Definitions`): the subgroup
`G_Σ ≤ G_K` that is the inverse image of the Frobenius closure `Γ` under
`G_K → G_K ⧸ I_L`, and the closed subgroup `Σ` of `G` whose underlying
subgroup is the image of `G_Σ` in `G`;
`DegreeData.frobeniusClosureDegree` (M014.028, from the sibling module
`Degree.FrobeniusFixedField.FrobeniusClosureDegree.Definitions` of this
contribution), the restriction `Γ →ₜ* ZHatMul` of the continuous normalized
degree to `Γ`; `DegreeData.normalizedDegree` (M011.006, from
`Degree.Frobenius.NormalizedDegree.Definitions`), the continuous
homomorphism `K.field.toSubgroup →ₜ* ZHatMul` (`ZHatMul`, M010.001, is
`Multiplicative ZHat`); the field `degree : G →ₜ* ZHatMul` of `DegreeData`
(M010.002); `DegreeData.FrobeniusElements` (M012.009),
`DegreeData.extensionInertiaWithin` (M012.002) and
`DegreeData.FiniteResidueAbstractField` (M010.021). `ClosedSubgroup`,
`Subgroup.map`, `Subgroup.subgroupOf`, `Subgroup.Normal`,
`ContinuousMonoidHom.toMonoidHom`, `MonoidHom.range`, quotient groups and
coset spaces, `Finite`, `CompactSpace` and `T2Space` are Mathlib's.

## Targets and complete telescopes

Both targets have the section binders implicit `{G : Type*}`, `[Group G]`
and `[TopologicalSpace G]`, with the single universe parameter `u_1`,
followed by the binders shown. The normality binder is the source binder
`[hLnormal : (extensionSubgroup K.field L hLK).Normal]` with the source
abbreviation `extensionSubgroup` (M004.002) expanded to its exact Mathlib
body.

```lean
def frobeniusFixedSubgroupWithin_normalizedDegree_imageStatement
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : Prop :=
    (D.frobeniusFixedSubgroupWithin K L hLK σ).map
        (D.normalizedDegree K).toMonoidHom =
      (D.frobeniusClosureDegree K L hLK σ).toMonoidHom.range
```

The image of `G_Σ` under the normalized degree of `K` equals the range of
the degree on `Γ`.

```lean
def frobeniusFixedField_relativeResidueQuotientFiniteStatement
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : Prop :=
    Finite
      (↥(K.field.toSubgroup.map D.degree.toMonoidHom) ⧸
        ((D.frobeniusFixedField K L hLK σ).toSubgroup.map
            D.degree.toMonoidHom).subgroupOf
          (K.field.toSubgroup.map D.degree.toMonoidHom))
```

If `G` is in addition compact and Hausdorff, the quotient of the degree
image of `G_K` by the degree image of `Σ` (as a subgroup of the former) is
finite.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. The statements are copied
   verbatim, apart from the `extensionSubgroup` expansion in the normality
   binders. The source proofs are omitted: this contribution publishes
   proposition targets, and their proofs are separate work.
3. Prefix each source docstring with `Target:`, and replace the source
   module docstring by a description of this module with a modification
   notice that names the source theorems.
4. Replace the source import by the published module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.Definitions`,
   the sibling module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosureDegree.Definitions`
   and the published module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.Definitions`
   (M011.006).
5. Omit `open CyclicCohomology`, which in these statements served only to
   resolve the expanded `extensionSubgroup`. Retain the noncomputable
   section, the variable line and the `DegreeData` namespace.
6. Omit all other source units, including the source-private theorem
   M016.016 `frobeniusFixedField_mappedRelIndex`, which the omitted proof of
   M016.018 uses. No helper declaration or instance is added.

The instance binders `[CompactSpace G]` and `[T2Space G]` of M016.018 are
retained although the proposition does not use them; they are hypotheses
of the source theorem, used by its proof.

These are the exact source statements as named propositions, without
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
