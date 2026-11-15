# NYLL M014.017, M014.019 and M014.021: targets about the continuous factorized normalized degree

The paired Lean file adapts the statements of three theorems from Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean`.
The pinned source file has SHA-256
`cda9dddf5f551fc8c81de825093b52cba99d644e45eb274682d2ee986585bfe3`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.DegreeData.` | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M014.017 | `extensionNormalizedDegreeContinuous_apply` (`@[simp]`, line 360) | 359 | 361–367 | 368 | `Langlands.NYLL.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_applyStatement` |
| M014.019 | `extensionNormalizedDegreeContinuous_surjective` | 380 | 381–386 | 387–390 | `Langlands.NYLL.ClassFormation.DegreeData.extensionNormalizedDegreeContinuous_surjectiveStatement` |
| M014.021 | `extensionDegreeKernelRestriction_injective` | 403 | 404–409 | 410–444 | `Langlands.NYLL.ClassFormation.DegreeData.extensionDegreeKernelRestriction_injectiveStatement` |

The enclosing source context is `namespace ClassFormation` (line 19),
`open CyclicCohomology` (line 21), `noncomputable section` (line 25),
`universe u` (line 27), the variables at line 29 and `namespace DegreeData`
(line 300).

The names used in the statements resolve to published `Langlands.NYLL`
declarations: `DegreeData.extensionNormalizedDegreeContinuous` and
`DegreeData.extensionDegreeKernelRestriction` (M014.016 and M014.020, from the
sibling module `NormalizedDegreeContinuous.Definitions`),
`DegreeData.extensionNormalizedDegree` (M012.005),
`DegreeData.extensionInertiaWithin` (M012.002) with its normality instance
(M012.003), `DegreeData.FiniteResidueAbstractField` (M010.021), `DegreeData`
(M010.002) and `ZHatMul` (M010.001). `ClosedSubgroup`, `Subgroup.subgroupOf`,
`Subgroup.Normal`, the quotient group, `Function.Surjective` and
`Function.Injective` are Mathlib's.

## Targets and complete telescopes

Every target has the section binders implicit `{G : Type u}`, `[Group G]`
and `[TopologicalSpace G]`, with the single universe parameter `u`, followed
by the explicit and instance binders shown. The normality binder
`[hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]` is the
source binder `[hLnormal : (extensionSubgroup K.field L hLK).Normal]` with
the source abbreviation `extensionSubgroup` (M004.002) expanded to its exact
Mathlib body, as in the sibling Definitions module. Write `G_K` for
`K.field.toSubgroup` and `G(\widetilde L|K)` for the quotient
`K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK`.

```lean
def extensionNormalizedDegreeContinuous_applyStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (x : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) : Prop :=
  D.extensionNormalizedDegreeContinuous K L hLK x =
    D.extensionNormalizedDegree K L hLK x
```

For every `x ∈ G(\widetilde L|K)`, the continuous factorized normalized degree
and the algebraic factorized normalized degree (M012.005) take the same value
at `x`.

```lean
def extensionNormalizedDegreeContinuous_surjectiveStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] : Prop :=
  Function.Surjective
    (D.extensionNormalizedDegreeContinuous K L hLK)
```

The continuous factorized normalized degree
`d_K : G(\widetilde L|K) → ℤ̂` is surjective.

```lean
def extensionDegreeKernelRestriction_injectiveStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] : Prop :=
  Function.Injective
    (D.extensionDegreeKernelRestriction K L hLK)
```

Restriction from the kernel of `d_K` on `G(\widetilde L|K)` to
`G(L|K) = G_K / G_L` is injective: an element of `G(\widetilde L|K)` that has
normalized degree one and restricts trivially to `G(L|K)` is trivial.

Binder order and kinds are those of the source theorems. No target has any
further hypothesis.

## Modification record

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the published names above.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. The statements are copied
   verbatim, apart from the `extensionSubgroup` expansion in the binders.
   The source proofs are omitted: this contribution publishes proposition
   targets, and their proofs are separate work.
3. Omit the `@[simp]` attribute of `extensionNormalizedDegreeContinuous_apply`,
   which cannot apply to a proposition-valued definition.
4. Replace each source docstring by a description of the proposition, and
   replace the source module docstring by a description of this module with
   a modification notice that names the source theorems.
5. Replace the source imports by the single focused import
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.NormalizedDegreeContinuous.Definitions`.
6. Omit `open CyclicCohomology`, which in these statements served only to
   resolve the expanded `extensionSubgroup`. Retain the noncomputable
   section, the universe declaration and the variable line.
7. Omit all other source units, including M014.018
   `extensionNormalizedDegreeContinuous_toMonoidHom`. No helper declaration or
   instance is added.

These are the exact source statements as named propositions, without
published proofs. They discharge no host class-formation, cup, transfer,
Tate or reciprocity target.

## Verification

The module passed a project Lean service check on 14 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), with no errors or warnings.
Declaration inspection reported `statement_returns_prop: true`, the single
universe parameter `u` and the axioms `propext`, `Classical.choice` and
`Quot.sound` for each target. Compilation and inspection are separate from
independent semantic acceptance and publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
