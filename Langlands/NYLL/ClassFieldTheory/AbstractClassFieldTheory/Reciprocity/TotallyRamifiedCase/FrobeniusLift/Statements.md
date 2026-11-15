# NYLL M079.001: degree-one Frobenius lifts in totally ramified extensions

The paired Lean file adapts the statement of the theorem `exists_degreeOneFrobeniusLiftOfTotallyRamified` of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FrobeniusLift.lean`.
The pinned source file has SHA-256
`f79c5d05f2fee424f3f4c8525bd9f3af253c5a7955f883d5d235deb2bae3729a`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.DegreeData.` | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M079.001 | `exists_degreeOneFrobeniusLiftOfTotallyRamified` | 30–31 | 32–40 | 40–112 | `Langlands.NYLL.ClassFormation.DegreeData.exists_degreeOneFrobeniusLiftOfTotallyRamifiedStatement` |

The enclosing source context is `noncomputable section` (line 18),
`namespace ClassFormation` (line 20), `open KummerTheory` and
`open CyclicCohomology` (lines 22–23), the comment at line 25, the variables
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` (line 26) and
`namespace DegreeData` (line 28). The rest of the source file (from line 113)
is not part of this module.

The names used in the statement resolve to `Langlands.NYLL` declarations:

- `IntegralRepGroupType` (M002.001), the abbreviation `Type 0`;
- `DegreeData` (M010.002) and `DegreeData.FiniteResidueAbstractField`
  (M010.021), whose field `field` is a closed subgroup `G_K`;
- `DegreeData.GaloisSubextension K.field` (M010.052, from
  `Degree.Fields.GaloisSubextension.Definitions`), a Galois extension `L`
  of `K` with fields `L.field`, `L.below` and `L.normal`, whose normality
  instance M010.057 makes the Frobenius objects below well-formed; in the
  same module, `GaloisSubextension.IsTotallyRamified` (M010.056): the degree
  image of `G_K` is contained in the degree image of `G_L`;
  `GaloisSubextension.extensionQuotient` (M010.054), the quotient
  `G_K ⧸ G_L` with group instance M010.058; and
  `GaloisSubextension.extensionQuotientMulEquiv` (M010.059), the identity
  multiplicative equivalence from `L.extensionQuotient` to
  `K.field.toSubgroup ⧸ L.field.toSubgroup.subgroupOf K.field.toSubgroup`;
- `DegreeData.FrobeniusElements` (M012.009) and
  `DegreeData.frobeniusRestriction` (M012.010), both from
  `Degree.FrobeniusLift.FrobeniusElements.Definitions`: the elements `σ` of
  `G_K ⧸ I_L` whose normalized degree is `ofAdd 1 ^ n` for some natural
  `n > 0`, and the map sending `σ` to its image in `G_K ⧸ G_L`;
- `DegreeData.frobeniusExponent` (M014.012, from
  `Degree.FrobeniusFixedField.FrobeniusClosure.Definitions`), the exponent
  `n` chosen (by `Exists.choose`) for a Frobenius element.

`MulEquiv.symm` is Mathlib's.

## Target and complete telescope

The target has the binders implicit `{G : IntegralRepGroupType}`,
`[Group G]` and `[TopologicalSpace G]`, followed by:

```lean
def exists_degreeOneFrobeniusLiftOfTotallyRamifiedStatement
    (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : GaloisSubextension K.field)
    (hTot : L.IsTotallyRamified D)
    (q : L.extensionQuotient) : Prop :=
    ∃ σ : D.FrobeniusElements K L.field L.below,
      D.frobeniusExponent K L.field L.below σ = 1 ∧
      L.extensionQuotientMulEquiv.symm
        (D.frobeniusRestriction K L.field L.below σ) = q
```

Let `K` be a field with finite residue quotient and `L | K` a totally
ramified Galois extension. Every element `q` of `G(L/K)` has a Frobenius
lift of exponent one: there is a Frobenius element `σ` of `G_K ⧸ I_L` whose
chosen exponent is `1` and whose restriction to `G(L/K)` is `q`.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace `theorem exists_degreeOneFrobeniusLiftOfTotallyRamified … : statement := proof`
   by `def exists_degreeOneFrobeniusLiftOfTotallyRamifiedStatement … : Prop := statement`.
   The statement is copied verbatim. The source proof is omitted: this
   contribution publishes the proposition target, and its proof is separate
   work.
3. Prefix the source docstring with `Target:`. Replace the source module
   docstring by a description of this module with a modification notice
   that names the source theorem.
4. Replace the source import by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Definitions`
   (M014.012, which also brings M012.009, M012.010 and M010.021),
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.GaloisSubextension.Definitions`
   (M010.052, M010.054, M010.056–M010.059) and
   `Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse` (M002.001).
5. Omit `open KummerTheory` and `open CyclicCohomology`, which the
   statement does not use. Retain the noncomputable section (left open at
   the end of the file, as in the source), the comment, the variable line
   and the namespaces.
6. Precede the definition by `set_option linter.unusedVariables false in`.
   The proposition does not mention the hypothesis `hTot`, and without this
   option the unused-variable linter warns about it. The option changes no
   declaration. `hTot` is retained because it is a hypothesis of the source
   theorem, used by its proof (through
   `GaloisSubextension.isTotallyRamified_iff_image_le`).
7. No helper declaration or instance is added.

These are exact source statements as named propositions, without
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
