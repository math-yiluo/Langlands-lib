# NYLL M031.002: the Frobenius fixed field is finite over the base field

The paired Lean file adapts the statement of one theorem from Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityDefinition.lean`.
The pinned source file has SHA-256
`929ff5558cef89ee325a04e4c0be9b4698d1430d445b5d13b4acc332998d3cb8`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.DegreeData.` | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M031.002 | `frobeniusFixedField_absoluteFinite` | 55 | 56–75 | 75–88 | `Langlands.NYLL.ClassFormation.DegreeData.frobeniusFixedField_absoluteFiniteStatement` |

The enclosing source context is `universe u` (line 21),
`namespace ClassFormation` (line 23), `open KummerTheory` (line 25),
`open CyclicCohomology` (line 27), `noncomputable section` (line 31),
`section frobeniusFixedFields` (line 33), the variables at line 35 and
`namespace DegreeData` (line 37).

The names used in the statement resolve to `Langlands.NYLL` declarations:
`DegreeData.frobeniusFixedField` (M016.004, from
`Reciprocity.Construction.FrobeniusField.Definitions`), the closed subgroup
`Σ` of `G` whose underlying subgroup is the image in `G` of the inverse
image `G_Σ ≤ G_K` of the Frobenius closure under `G_K → G_K ⧸ I_L`;
`DegreeData.FrobeniusElements` (M012.009), the elements `σ` of
`G_K ⧸ I_L` whose normalized degree is `ofAdd 1 ^ n` for some natural
`n > 0`; `FiniteAbstractField` (M010.121), a closed subgroup `field` of `G`
of finite index in the base; `FiniteAbstractField.toFiniteResidueAbstractField`
(M010.126, from `Degree.Fields.FiniteAbstractField.Residue.Definitions`),
which regards such a field, with the same closed subgroup `field`, as a
`DegreeData.FiniteResidueAbstractField D` (M010.021); and `baseField G`
(M010.003), the closed subgroup `⊤` of `G` representing the base field `k`.
`ClosedSubgroup`, `Subgroup.subgroupOf`, `Subgroup.Normal`, quotient groups
and coset spaces, `Finite`, `CompactSpace`, `T2Space`,
`IsTopologicalGroup` and `simpa` are Mathlib's or Lean's.

## Target and complete telescope

The target has the section binders implicit `{G : Type u}`, `[Group G]` and
`[TopologicalSpace G]`, with the single universe parameter `u`, followed by
the binders shown. Each source application `extensionSubgroup A B h` of the
abbreviation M004.002 is expanded to its exact Mathlib body
`B.toSubgroup.subgroupOf A.toSubgroup`. In the conclusion this drops the
proof argument `le_baseField (D.frobeniusFixedField …)` (M010.005), which
the abbreviation body does not use.

```lean
def frobeniusFixedField_absoluteFiniteStatement (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK
      (hLnormal := by
        simpa only [FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal)) :
    Prop :=
    Finite ((baseField G).toSubgroup ⧸
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK
          (hLnormal := by
            simpa only [FiniteAbstractField.toFiniteResidueAbstractField] using hLnormal)
          σ).toSubgroup.subgroupOf
        (baseField G).toSubgroup)
```

Let `G` be a compact Hausdorff topological group with degree data `D`, let
`K` be a field finite over the base field `k` and `L` a closed subgroup of
`G_K` that is normal of finite index in it. For a Frobenius element `σ`
(over `K` regarded as a field with finite residue quotient), the fixed
field `Σ` of `σ` is finite over `k`: the subgroup of `Σ` has finite index
in `G = G_k`.

The named arguments `(hLnormal := by simpa only [...] using hLnormal)` are
copied from the source. They supply the normality instance for
`(K.toFiniteResidueAbstractField D).field`, which is `K.field` by
definition, from the binder `hLnormal`. Because `Normal` is a proposition,
the elaborated statement does not depend on which proof the tactic builds.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. The statement is copied
   verbatim, apart from the `extensionSubgroup` expansions described above.
   The source proof is omitted: this contribution publishes a proposition
   target, and its proof is separate work.
3. Prefix the source docstring with `Target:` and reword it ("finiteness of
   `Σ | k` for the fixed field `Σ` of a Frobenius element over a finite
   abstract field `K`" for "Finiteness of `Σ | k`, obtained from the finite
   tower `Σ | K | k`", whose second half describes the omitted proof), and
   replace the source module docstring by a description of this module
   with a modification notice that names the source theorem.
4. Replace the source imports by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.Definitions`
   (M016.004; M012.009 and M010.021 come through its imports) and
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Residue.Definitions`
   (M010.126; M010.121 and M010.003 come through its imports).
5. Omit `open KummerTheory` and `open CyclicCohomology`; the latter served
   only to resolve the expanded `extensionSubgroup`, and the former is not
   used by the statement. Retain the universe declaration, the
   noncomputable section, the section `frobeniusFixedFields`, the variable
   line and the `DegreeData` namespace.
6. Precede the definition by `set_option linter.unusedVariables false in`.
   The proposition does not mention the instance hypothesis `hLfinite`, and
   without this option the unused-variable linter warns about it. The option
   changes no declaration.
7. Omit all other source units, including the definition
   `frobeniusFixedIntermediateField` (lines 39–53) and everything after
   line 92. No helper declaration or instance is added.

The binders `[CompactSpace G]`, `[T2Space G]` and `hLfinite` are retained
although the proposition does not use them; they are hypotheses of the
source theorem, used by its proof.

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
