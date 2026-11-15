# NYLL M027.001: conjugating an abstract field does not change its degree image

The paired Lean file adapts the statement of one theorem of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/ValuationLaws.lean`.
The pinned source file has SHA-256
`f540072f238d978f402034f3404bdaca624ff649cddf81e41cd8b9c7f73b68f8`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.` | Docstring | Telescope and statement | Proof | Adapted target after `Langlands.NYLL.ClassFormation.` |
| --- | --- | --- | --- | --- | --- |
| M027.001 | `DegreeData.fieldImage_conjugate` | 31 | 32–35 | 35–51 | `DegreeData.fieldImage_conjugateStatement` |

The source context is `namespace ClassFormation` (line 17),
`open KummerTheory` (line 19), `open CyclicCohomology` (line 21),
`noncomputable section` (line 25) and the variables
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (line 28) and
`{D : DegreeData G} {A : Rep ℤ G}` (line 29). The source theorem binds its
own `{G : Type*}` and `(D : DegreeData G)`, which shadow the variables, and
mentions neither `A` nor any other variable, so no variable of lines 28–29
is part of its telescope. The source imports are the NYLL modules
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation` and
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws` (lines 7–8).
The other declarations of the source file are outside this contribution.

The statement uses these published declarations:

- `DegreeData G` (M010.002, from `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`), the
  degree datum: a continuous homomorphism `degree : G →ₜ* ZHatMul`, where
  `ZHatMul` is `Multiplicative ZHat`, with `degree_surjective`;
- `D.fieldImage K` (M010.010, from `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`), the
  image `d(G_K)` of the restricted degree, a subgroup of `ZHatMul`;
- `conjugateClosedSubgroup K σ` (M026.001, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Definitions`), the closed subgroup of `G` whose
  underlying subgroup is `ConjAct.toConjAct σ⁻¹ • K.toSubgroup`, that is
  `σ⁻¹ G_K σ`, the subgroup of the right conjugate field `K^σ`;
- Mathlib's `ClosedSubgroup G`, with its underlying subgroup
  `K.toSubgroup` and the subspace topology on `K.toSubgroup`.

The module imports `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Definitions`, which imports
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`.

## Target and complete telescope

The telescope shown is complete.

```lean
def DegreeData.fieldImage_conjugateStatement
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (D : DegreeData G) (K : ClosedSubgroup G) (σ : G) : Prop :=
    D.fieldImage (conjugateClosedSubgroup K σ) = D.fieldImage K
```

For a degree datum `D` on a topological group `G` with continuous
multiplication, a closed subgroup `K` and `σ : G`, the degree image of the
conjugate field `K^σ`, whose subgroup is `σ⁻¹ G_K σ`, equals that of `K`.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the target is
   `Langlands.NYLL.ClassFormation.DegreeData.fieldImage_conjugateStatement`.
2. Replace `theorem DegreeData.fieldImage_conjugate … : statement := proof`
   by `def DegreeData.fieldImage_conjugateStatement … : Prop := statement`.
   The telescope and the statement are copied verbatim, including the
   binder names, kinds and order. The source proof is omitted: this
   contribution publishes the proposition target, and its proof is
   separate work.
3. Prefix the source docstring with `Target:` and lower-case the first word
   after it; the wording is otherwise unchanged. Replace the source module
   docstring by a description of this module with a modification notice.
4. Replace the source imports by the focused published import above.
5. Keep the namespace and the noncomputable section; omit the opens, the
   variable lines 28–29, which the theorem does not use, and the rest of the
   source file.
6. No helper declaration, instance or linter option is added.

This is the exact source statement as a named proposition, without a
published proof. It discharges no host class-formation, cup, transfer, Tate or reciprocity
target.

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
