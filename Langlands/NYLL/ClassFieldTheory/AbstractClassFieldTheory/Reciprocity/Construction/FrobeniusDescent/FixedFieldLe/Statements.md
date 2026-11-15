# NYLL M017.004: a Frobenius lift with trivial restriction has fixed field containing `L`

The paired Lean file adapts the statement of one theorem from Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusDescent.lean`.
The pinned source file has SHA-256
`75b2b32aeb8d07b1534b1ceb6c60052c71544a6029e1bc519c88905d9f63495f`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.DegreeData.` | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M017.004 | `frobeniusFixedField_le_of_restriction_eq_one` | 135–136 | 137–147 | 147–181 | `Langlands.NYLL.ClassFormation.DegreeData.frobeniusFixedField_le_of_restriction_eq_oneStatement` |

The enclosing source context is `namespace ClassFormation` (line 19),
`open CyclicCohomology` (line 21), `noncomputable section` (line 25), the
variables at line 27 and `namespace DegreeData` (line 29). The source file
has no universe declaration.

The names used in the statement resolve to `Langlands.NYLL` declarations:
`DegreeData.frobeniusFixedField` (M016.004, from
`Reciprocity.Construction.FrobeniusField.Definitions`), the closed subgroup
`Σ` of `G` whose underlying subgroup is the image in `G` of the inverse
image `G_Σ ≤ G_K` of the Frobenius closure under `G_K → G_K ⧸ I_L`;
`DegreeData.FrobeniusElements` (M012.009, from
`Degree.FrobeniusLift.FrobeniusElements.Definitions`), the elements `σ` of
`G_K ⧸ I_L` whose normalized degree is `ofAdd 1 ^ n` for some natural
`n > 0`; `DegreeData.frobeniusRestriction` (M012.010, same module), the
map sending such `σ` to its image in `G_K ⧸ G_L`, namely
`extensionRestriction K.field L hLK σ.1` (M012.007); and
`DegreeData.FiniteResidueAbstractField` (M010.021), whose field `field` is
a closed subgroup `G_K` of `G`. `ClosedSubgroup`, `Subgroup.subgroupOf`,
`Subgroup.Normal`, the order on subgroups, quotient groups and coset
spaces, `Finite`, `CompactSpace`, `T2Space` and `IsTopologicalGroup` are
Mathlib's.

## Target and complete telescope

The target has the section binders implicit `{G : Type*}`, `[Group G]` and
`[TopologicalSpace G]`, with the single universe parameter `u_1`, followed
by the binders shown. In the normality and finiteness binders the source
abbreviation `extensionSubgroup K.field L hLK` (M004.002) is expanded to its
exact Mathlib body `L.toSubgroup.subgroupOf K.field.toSubgroup`.

```lean
def frobeniusFixedField_le_of_restriction_eq_oneStatement
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements K L hLK)
    (hσ : D.frobeniusRestriction K L hLK σ = 1) : Prop :=
    (D.frobeniusFixedField K L hLK σ).toSubgroup ≤
      L.toSubgroup
```

Let `G` be a compact Hausdorff topological group with degree data `D`, let
`K` be a field with finite residue quotient and `L` a closed subgroup of
`G_K` that is normal of finite index in it. If a Frobenius element `σ` of
`G_K ⧸ I_L` restricts to `1` in `G_K ⧸ G_L`, then the subgroup of the fixed
field `Σ` of `σ` lies in `G_L`; in field terms, `Σ` contains `L`.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. The statement is copied
   verbatim, apart from the `extensionSubgroup` expansion in the normality
   and finiteness binders. The source proof is omitted: this contribution
   publishes a proposition target, and its proof is separate work.
3. Prefix the source docstring with `Target:` and reword it slightly
   ("the closed subgroup of the fixed field lies in `G_L`" for
   "equivalently `G_Σ ≤ G_L`"), and replace the source module docstring by
   a description of this module with a modification notice that names the
   source theorem.
4. Replace the source imports by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.Definitions`
   (M016.004) and
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.FrobeniusElements.Definitions`
   (M012.009, M012.010).
5. Omit `open CyclicCohomology`, which in this statement served only to
   resolve the expanded `extensionSubgroup`. Retain the noncomputable
   section, the variable line and the `DegreeData` namespace.
6. Precede the definition by `set_option linter.unusedVariables false in`.
   The proposition does not mention the hypotheses `hLfinite` and `hσ`, and
   without this option the unused-variable linter warns about them. The
   option changes no declaration.
7. Omit all other source units, including the source definition
   `extensionImageInInertiaQuotient` and the theorem
   `extensionImageInInertiaQuotient_isClosed` that the omitted proof uses.
   No helper declaration or instance is added.

The binders `[CompactSpace G]`, `[T2Space G]`, `hLfinite` and `hσ` are
retained although the proposition does not use them; they are hypotheses of
the source theorem, used by its proof.

This is the exact source statement as a named proposition, without a
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
