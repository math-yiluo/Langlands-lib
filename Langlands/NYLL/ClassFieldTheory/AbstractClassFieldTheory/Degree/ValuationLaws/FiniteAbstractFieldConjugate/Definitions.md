# NYLL M027.004: the conjugate of a finite abstract field

The paired Lean file adapts one definition of Naganori
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

| Unit | Source definition after `ClassFormation.` | Docstring | Definition | Adapted name after `Langlands.NYLL.ClassFormation.` |
| --- | --- | --- | --- | --- |
| M027.004 | `FiniteAbstractField.conjugate` | 84–85 | 86–94 | `FiniteAbstractField.conjugate` |

The source context is `namespace ClassFormation` (line 17),
`open KummerTheory` (line 19), `open CyclicCohomology` (line 21),
`noncomputable section` (line 25) and the variables
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (line 28, after
the comment line 27) and `{D : DegreeData G} {A : Rep ℤ G}` (line 29). The
definition binds its own `{G : Type*}`, which shadows the variable of line
28, and mentions neither `D` nor `A`, so no variable of lines 28–29 is part
of its telescope. The source imports are the NYLL modules
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation` and
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws` (lines 7–8).
The other declarations of the source file are outside this contribution.

The definition uses these declarations:

- `FiniteAbstractField G` (M010.121, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Definitions`), the structure of a
  closed subgroup `field` with a proof `finite` that
  `(baseField G).toSubgroup ⧸ extensionSubgroup (baseField G) field
  (le_baseField field)` is finite: an abstract field of finite degree over
  the base;
- `absoluteConjugateCosetEquiv K σ` (M026.007, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.AbsoluteConjugate.Definitions`, contributed together
  with this module), the equivalence of the absolute coset spaces
  `G ⧸ G_{K^σ}` and `G ⧸ G_K`;
- `conjugateClosedSubgroup K σ` (M026.001, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Definitions`), the closed subgroup of `G` whose
  underlying subgroup is `ConjAct.toConjAct σ⁻¹ • K.toSubgroup`, that is
  `σ⁻¹ G_K σ`, the subgroup of the right conjugate field `K^σ`;
- `baseField G` (M010.003, from `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`), the closed
  subgroup `⊤` of `G`, the distinguished base field, and `le_baseField K`
  (M010.005, proved in `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs`), whose type
  `le_baseFieldStatement K` is `K.toSubgroup ≤ (baseField G).toSubgroup`;
- `CyclicCohomology.extensionSubgroup K L hLK` (M004.002, from
  `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`,
  available through `open CyclicCohomology`), the abbreviation
  `L.toSubgroup.subgroupOf K.toSubgroup`, that is `G_L` as a subgroup of
  `G_K`;
- Mathlib's `ClosedSubgroup G` and `Finite.of_equiv`.

The module imports `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Definitions` and
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.AbsoluteConjugate.Definitions`.

## Definition and complete telescope

The telescope shown is complete.

```lean
noncomputable def FiniteAbstractField.conjugate
    {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G] (K : FiniteAbstractField G) (σ : G) :
    FiniteAbstractField G where
  field := conjugateClosedSubgroup K.field σ
  finite := Finite.of_equiv
    ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K.field (le_baseField K.field))
    (absoluteConjugateCosetEquiv K.field σ).symm
```

For a finite abstract field `K` and `σ : G`, this is the finite abstract
field with subgroup `σ⁻¹ G_K σ` (the right conjugate `K^σ`), whose
finiteness over the base is transported from that of `K` along
`(absoluteConjugateCosetEquiv K.field σ).symm`.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the definition is
   `Langlands.NYLL.ClassFormation.FiniteAbstractField.conjugate`.
2. Copy the docstring, the binders and the body verbatim.
3. Replace the source imports by the two focused published imports above
   and the source module docstring by a description of this module with a
   modification notice.
4. Keep the namespace, both opens (`open CyclicCohomology` makes
   `extensionSubgroup` available) and the noncomputable section; omit the
   comment line 27, the variable lines 28–29, which the definition does not
   use, and the rest of the source file.
5. No helper declaration, instance or linter option is added.

It discharges no host class-formation, cup, transfer, Tate or reciprocity
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
