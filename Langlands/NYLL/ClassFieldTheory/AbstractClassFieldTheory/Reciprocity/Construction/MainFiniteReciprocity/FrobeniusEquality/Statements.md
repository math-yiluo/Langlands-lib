# NYLL M065.010: equal restriction and exponent give equal Frobenius lifts

The paired Lean file adapts the statement of the theorem `frobenius_eq_of_restriction_eq_of_exponent_eq` of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainFiniteReciprocity.lean`.
The pinned source file has SHA-256
`aa0954d0883cd84c712e46b9bdd98456a21cad95119a37acc3164141fc539bad`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.DegreeData.` | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M065.010 | `frobenius_eq_of_restriction_eq_of_exponent_eq` | 311–312 | 313–322 | 322–326 | `Langlands.NYLL.ClassFormation.DegreeData.frobenius_eq_of_restriction_eq_of_exponent_eqStatement` |

The enclosing source context is `universe u` (line 29),
`namespace ClassFormation` (line 31), `open KummerTheory` (line 33),
`open CyclicCohomology` (line 35), `open CategoryTheory` (line 37),
`open scoped BigOperators` (line 38), `noncomputable section` (line 43),
`section equalFrobeniusLifts` (lines 305–330), the variables
`{G : Type u} [Group G] [TopologicalSpace G]` (line 307) and
`namespace DegreeData` (lines 309–328). The source imports (lines 7–14) are
eight modules of
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity`;
the rest of the source file is not part of this module.

The names used resolve to `Langlands.NYLL` declarations:

- `DegreeData` (M010.002) and `DegreeData.FiniteResidueAbstractField D`
  (M010.021);
- `DegreeData.FrobeniusElements` (M012.009) and
  `DegreeData.frobeniusRestriction` (M012.010, both from
  `Degree.FrobeniusLift.FrobeniusElements.Definitions`): the subtype of
  elements of `G_K ⧸ (G_L ⊓ I_K)` with positive natural normalized degree,
  and their images in `G_K ⧸ G_L`;
- `DegreeData.frobeniusExponent` (M014.012, from
  `Degree.FrobeniusFixedField.FrobeniusClosure.Definitions`), the chosen
  positive natural `n` with normalized degree `(Multiplicative.ofAdd 1) ^ n`;
- `CyclicCohomology.extensionSubgroup` (M004.002), the abbreviation
  `L.toSubgroup.subgroupOf K.toSubgroup`.

## Target and complete telescope

The target has the binders implicit `{G : Type u}`, `[Group G]` and
`[TopologicalSpace G]`, followed by:

```lean
def frobenius_eq_of_restriction_eq_of_exponent_eqStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    {σ τ : D.FrobeniusElements K L hLK}
    (hRestriction : D.frobeniusRestriction K L hLK σ =
      D.frobeniusRestriction K L hLK τ)
    (hExponent : D.frobeniusExponent K L hLK σ =
      D.frobeniusExponent K L hLK τ) : Prop :=
    σ = τ
```

Two Frobenius elements of `G_K ⧸ (G_L ⊓ I_K)` with the same image in
`G_K ⧸ G_L` and the same Frobenius exponent are equal.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace `theorem frobenius_eq_of_restriction_eq_of_exponent_eq … : statement := proof`
   by `def frobenius_eq_of_restriction_eq_of_exponent_eqStatement … : Prop := statement`.
   The statement is copied verbatim. The source proof is omitted: this
   contribution publishes the proposition target, and its proof is separate
   work.
3. Prefix the source docstring with `Target:`. Replace the source module
   docstring by a description of this module with a modification notice
   that names the source theorem.
4. Put `set_option linter.unusedVariables false in` before the target. The
   proposition does not mention `hRestriction` and `hExponent`, and the
   linter would otherwise warn; the option changes no declaration.
5. Replace the source import by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Definitions`
   (M014.012, which also brings M010.002, M010.021, M012.009 and M012.010)
   and `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`
   (M004.002).
6. Omit the other declarations of the source file, the section
   `equalFrobeniusLifts` (its variable line is kept) and the unused
   `open KummerTheory`, `open CategoryTheory` and `open scoped BigOperators`.
   Retain the universe, `open CyclicCohomology`, the noncomputable section
   and the namespaces.
7. No helper declaration or instance is added.

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
