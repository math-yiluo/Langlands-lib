# The Frobenius fixed field is finite over the base field

This module proves the theorem
`Langlands.NYLL.ClassFormation.DegreeData.frobeniusFixedField_absoluteFinite`, the proof phase of
M031.002 in the
[NYLL partition](../../../../../../../../../notes/reuse/nyll-public-port/m025-m048.md#m031).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.frobeniusFixedField_absoluteFiniteStatement` applied to the
theorem's parameters:

```lean
theorem frobeniusFixedField_absoluteFinite (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK
      (hLnormal := by
        simpa only [FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal)) :
    frobeniusFixedField_absoluteFiniteStatement D K L hLK σ
```

## Target and binders

The theorem has the binders of the published target, in the same order: the section variables `{G : Type u} [Group G] [TopologicalSpace G]`, then `D : DegreeData G` (M010.002), `[IsTopologicalGroup G] [CompactSpace G] [T2Space G]`, `K : FiniteAbstractField G`, a closed subgroup `L` with `hLK : L.toSubgroup ≤ K.field.toSubgroup`, the instances `hLnormal` and `hLfinite`, and a Frobenius lift `σ` over `K.toFiniteResidueAbstractField D`, whose normality argument is the source's named-argument proof. The source writes each subgroup `extensionSubgroup A B h` as such; the published target uses its abbreviation body `B.toSubgroup.subgroupOf A.toSubgroup`.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityDefinition.AbsoluteFinite.Statements`, the target is the proposition

```lean
Finite ((baseField G).toSubgroup ⧸
  (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
      (hLnormal := by
        simpa only [FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal)
      σ).toSubgroup.subgroupOf
    (baseField G).toSubgroup)
```

That is, for a finite abstract field `K` (M010.121) and a Frobenius lift `σ` over its residue-field package `K.toFiniteResidueAbstractField D` (M010.126), the Frobenius fixed field `Σ` (M016.004) is finite over the distinguished base field `k = baseField G` (M010.003): `G_Σ`, read inside `G_k`, has finite index. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityDefinition.AbsoluteFinite.Statements`, which defines the target and imports the published definitions `frobeniusFixedField` (M016.004), `FiniteAbstractField` (M010.121), `toFiniteResidueAbstractField` (M010.126) and `baseField` (M010.003), with the published instance M010.125 that `G_k ⧸ G_K` is finite for a finite abstract field `K`;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.U010.Proofs`, the proof of M016.010 `frobeniusFixedField_finite` in this task;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U014.Proofs`, the published proof of M026.014 `relativeTowerQuotientFinite`: in a tower `M ≤ L ≤ K` of closed subgroups with `K ⧸ L` and `L ⧸ M` finite, `K ⧸ M` is finite;
- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs`, the published proof of M010.005 `le_baseField`: every closed subgroup lies in `baseField G`.

The module opens `CyclicCohomology`, as the source does, in whose namespace `extensionSubgroup` (M004.002) lies; the published statement of M026.014 is written with it.

## Implemented proof

The proof follows the source. With `KR = K.toFiniteResidueAbstractField D`, it transports the instances `hLnormal` and `hLfinite` to `KR` (whose field is `K.field` by definition) as local instances, makes `K.field ⧸ G_Σ` finite by M016.010 for `KR`, and concludes with M026.014 for the tower `G_Σ ≤ G_K ≤ G_k`, whose two inclusions are `G_Σ ≤ G_K` and `le_baseField K.field` (M010.005); the finiteness of `G_k ⧸ G_K` is found by instance search from the published instance M010.125, as in the source. The inclusion `G_Σ ≤ G_K` is M016.006 `frobeniusFixedField_le` in the source, whose proof is not in the Library; the module proves it as the local fact `hle` by its source proof (`rintro g ⟨k, _, rfl⟩; exact k.2`), with a comment.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityDefinition.lean`, lines 55–88](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityDefinition.lean#L55-L88):
the docstring at line 55 and the theorem at lines 56–88. It lies in `namespace ClassFormation` (line 23), after `universe u` (line 21), with `open KummerTheory` (line 25), `open CyclicCohomology` (line 27), its `noncomputable section` (line 31), `section frobeniusFixedFields` (line 33), the variables `{G : Type u} [Group G] [TopologicalSpace G]` (line 35) and `namespace DegreeData` (line 37). The inlined M016.006 is at lines 100–108 of `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean`. The source is:

```lean
/-- Finiteness of `Σ | k`, obtained from the finite tower `Σ | K | k`. -/
theorem frobeniusFixedField_absoluteFinite (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK
      (hLnormal := by
        simpa only [FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal)) :
    Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G)
        (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
          (hLnormal := by
            simpa only [FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal) σ)
        (le_baseField
          (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
            (hLnormal := by
              simpa only [FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal) σ)))
                := by
  let KR := K.toFiniteResidueAbstractField D
  let hLnormalKR : (extensionSubgroup KR.field L hLK).Normal := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal
  let hLfiniteKR : Finite
      (KR.field.toSubgroup ⧸ extensionSubgroup KR.field L hLK) := by
    simpa only [KR, FiniteAbstractField.toFiniteResidueAbstractField] using hLfinite
  let : Finite (K.field.toSubgroup ⧸
      extensionSubgroup K.field (D.frobeniusFixedField KR L hLK σ)
        (D.frobeniusFixedField_le KR L hLK σ)) :=
    D.frobeniusFixedField_finite KR L hLK σ
  exact relativeTowerQuotientFinite (baseField G) K.field
    (D.frobeniusFixedField KR L hLK σ)
    (D.frobeniusFixedField_le KR L hLK σ) (le_baseField K.field)
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityDefinition.lean`;
its SHA-256 is `929ff5558cef89ee325a04e4c0be9b4698d1430d445b5d13b4acc332998d3cb8`.

Modifications by Worker 5264 on 15 November 2026:

- give the theorem the published proposition `frobeniusFixedField_absoluteFiniteStatement D K L hLK σ` as its type;
- replace the two uses of `D.frobeniusFixedField_le KR L hLK σ` (M016.006, not proved in the Library) by the local fact `hle`, proved by M016.006's source proof, with a comment; in the local finiteness instance the use disappears with the expansion below;
- give the local finiteness instance from M016.010, whose published type is its Statement proposition, the unfolded type;
- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- expand each `extensionSubgroup A B h` in the binders and the local instances to its abbreviation body `B.toSubgroup.subgroupOf A.toSubgroup`, as in the published target;
- omit `open KummerTheory`, the `noncomputable section` and all other source declarations; keep `universe u`, `open CyclicCohomology`, the section `frobeniusFixedFields` and the variable line.

The docstring, the binders and all other proof steps are the source's. The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; additional
attribution material is registered as `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright 2026
Naganori Yamaguchi, author “Naganori Yamaguchi (assisted by OpenAI Codex)”, released
under Apache-2.0. The Lean file carries the dated modification record. The unchanged
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in the
Library. No Mathlib code is copied.

This module proves only M031.002. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.
