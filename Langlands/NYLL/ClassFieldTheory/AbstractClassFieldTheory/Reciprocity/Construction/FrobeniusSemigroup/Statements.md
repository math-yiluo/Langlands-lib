# NYLL M015.003: target about the Frobenius semigroup

The paired Lean file adapts the statement of one theorem from Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusSemigroup.lean`.
The pinned source file has SHA-256
`d11fc29514c9a12171d2a10287d09d10aa13b765641c57893c102aa7a6a70a06`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.DegreeData.` | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M015.003 | `frobeniusMul_coe` (`@[simp]`, line 57) | 56 | 58–64 | 65 | `Langlands.NYLL.ClassFormation.DegreeData.frobeniusMul_coeStatement` |

The enclosing source context is `namespace ClassFormation` (line 16),
`open CyclicCohomology` (line 18), `noncomputable section` (line 22),
`namespace DegreeData` (line 24) and the variables at line 26. The source
file has no universe declaration.

The names used in the statement resolve to `Langlands.NYLL` declarations:
the instance `DegreeData.frobeniusElementsMul` (M015.002, defined through
`DegreeData.frobeniusMul`, M015.001), from the sibling module
`FrobeniusSemigroup.Definitions` of this contribution, which is the single
import here; `DegreeData.FrobeniusElements` (M012.009), the subtype of
`K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK` of elements
whose normalized degree is a strictly positive natural power of the
generator; `DegreeData.extensionInertiaWithin` (M012.002),
`DegreeData.FiniteResidueAbstractField` (M010.021) and `DegreeData`
(M010.002). `ClosedSubgroup`, `Subgroup.subgroupOf`, `Subgroup.Normal`,
quotient groups and subtype values `.1` are Mathlib's or Lean core's.

## Target and complete telescope

The target has the section binders implicit `{G : Type*}`, `[Group G]` and
`[TopologicalSpace G]`, with the single universe parameter `u_1`, followed
by the binders shown. The normality binder is the source binder
`[hLnormal : (CyclicCohomology.extensionSubgroup (G := G) K.field L hLK).Normal]`
with the source abbreviation `extensionSubgroup` (M004.002) expanded to its
exact Mathlib body.

```lean
def frobeniusMul_coeStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ τ : D.FrobeniusElements K L hLK) : Prop :=
    (σ * τ).1 = σ.1 * τ.1
```

For Frobenius elements `σ` and `τ`, the quotient element underlying their
product under the instance M015.002 is the product `σ.1 * τ.1` of their
underlying quotient elements.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace `theorem frobeniusMul_coe … : statement := proof` by
   `def frobeniusMul_coeStatement … : Prop := statement`. The statement is
   copied verbatim, apart from the `extensionSubgroup` expansion in the
   normality binder. The source proof `rfl` is omitted: this contribution
   publishes a proposition target, and its proof is separate work.
3. Omit the `@[simp]` attribute, which cannot apply to a
   proposition-valued definition.
4. Replace the source docstring by a description of the proposition
   beginning with `Target:`, and replace the source module docstring by a
   description of this module with a modification notice that names the
   source theorem.
5. Replace the source import by the sibling module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusSemigroup.Definitions`.
6. Omit `open CyclicCohomology`, which is not needed once
   `extensionSubgroup` is expanded. Retain the noncomputable section, the
   `DegreeData` namespace and the variable line.
7. Omit all other source units. No helper declaration or instance is added.

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
