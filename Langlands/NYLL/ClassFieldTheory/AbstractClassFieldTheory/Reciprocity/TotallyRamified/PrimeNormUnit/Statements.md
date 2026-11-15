# NYLL M083.002: a zero prime-norm class is the norm of a prime power times a unit

The paired Lean file adapts the statement of the theorem `ValuationData.primeNormClass_eq_zero_exists_unit_norm_eq` of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamified.lean`.
The pinned source file has SHA-256
`0294844f85bffa1a3b4bc255c93c644b01f9e43dcd863a5e64718af4abcc0cc2`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.ValuationData.` | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M083.002 | `primeNormClass_eq_zero_exists_unit_norm_eq` | 93–97 | 98–122 | 122–196 | `Langlands.NYLL.ClassFormation.ValuationData.primeNormClass_eq_zero_exists_unit_norm_eqStatement` |

The enclosing source context is `namespace ClassFormation` (lines 27–444),
`open KummerTheory` (line 29), `open CyclicCohomology` (line 31),
`noncomputable section` (lines 35–443), `open CategoryTheory` (line 37), the
comment and variables `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`
(lines 39–40), `namespace ValuationData` (lines 89–441) and the variables
`{D : DegreeData G} {A : Rep ℤ G}` (line 91). The only source import is the
unported module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core`
(line 7). The rest of the source file is not part of this module; the target
of M083.004 is published in `Reciprocity.TotallyRamified.Primitive.Statements`
and that of M083.003 in the sibling module
`Reciprocity.TotallyRamified.ActionValuation.Statements`.

The names used resolve to `Langlands.NYLL` declarations:

- `IntegralRepGroupType` (M002.001, from
  `GaloisCohomology.Cyclic.IntegralRepUniverse`), the abbreviation `Type 0`;
- `DegreeData G` (M010.002, from `Degree.Fields.Definitions`), a continuous
  surjective degree homomorphism `G →ₜ* ZHatMul` (`ZHatMul` is
  `Multiplicative ZHat`);
- `ValuationData D A` (M025.012, from
  `Degree.Valuation.ValuationData.Definitions`), a henselian valuation of the
  base-field fixed module, and `ValuationData.valueGroup` (M025.013, same
  module), its value group `v(A_k)`, an additive subgroup of `ZHat`;
- `ZHat` (M008.008, from
  `GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Definitions`), the
  profinite integers;
- `ValuationData.valuationAt v K` (M025.025, from
  `Degree.Valuation.ValuationData.Normalized.Definitions`), the normalized
  valuation `v_K = (1/f_K) v ∘ N_{K|k}` on `A^{G_K}`, an additive homomorphism
  into `v.valueGroup`;
- `FiniteAbstractField G` (M010.121, from
  `Degree.Fields.FiniteAbstractField.Definitions`), a closed subgroup
  `K.field` of finite index over the base field;
- `KummerTheory.ambientFixedAddSubgroup A H` (M023.001, from
  `GaloisCohomology.Kummer.Abstract.KummerDelta.U001.Definitions`), the
  additive subgroup `A^H` of elements of `A` fixed by `H`;
- `DegreeData.AbstractExtension G` (M010.028, from
  `Degree.Fields.AbstractExtension.Definitions`), whose constructor
  `DegreeData.AbstractExtension.mk field base below` takes two closed
  subgroups and the inclusion `field.toSubgroup ≤ base.toSubgroup`, and
  `DegreeData.AbstractExtension.IsTotallyRamified` (M010.045, from
  `Degree.Fields.AbstractExtension.StructuralDefinitions`): the degree image
  of the base is contained in the degree image of the field;
- `DegreeData.FiniteAbstractExtension.ofInclusion` (M010.068, from
  `Degree.Fields.FiniteExtension.Definitions`), the finite abstract
  extension `field | base` built from an inclusion and the instance that
  its coset space is finite, here `hSKfinite`, and
  `DegreeData.FiniteAbstractExtension.residueDegree` (M010.086, from
  `Degree.Fields.FiniteExtension.NumericDefinitions`), its positive relative
  residue degree;
- `CyclicCohomology.extensionSubgroup` (M004.002), the abbreviation
  `extensionSubgroup K L hLK = L.toSubgroup.subgroupOf K.toSubgroup`;
- `ValuationData.IsPrimeElement v K π` (M028.007) and
  `ValuationData.unitAddSubgroup v K` (M028.008, both from
  `Degree.PrimeElements.Prime.Definitions`): `v_K(π)` is the normalized value
  one, and the kernel `U_K` of `v_K`;
- `relativeNorm A K L hLK` (M024.009, from `Degree.Norm.RelativeNorm.Definitions`),
  the relative norm `A^{G_L} →+ A^{G_K}`, and `finiteNormClass A K L hLK`
  (M039.006, from `Reciprocity.Construction.FiniteNormQuotient.Definitions`),
  the class of an element of `A^{G_K}` in `A^{G_K} ⧸ N_{L|K} A^{G_L}`; both
  take the finiteness of `G_K ⧸ G_L` as an instance argument, supplied by
  `hLKfinite` and `hSKfinite`.

`Rep ℤ G` and the scalar multiplication `ℕ • _` are Mathlib's.

## Target and complete telescope

The target has the binders implicit `{G : IntegralRepGroupType}`,
`[Group G]`, `[TopologicalSpace G]`, `{D : DegreeData G}` and
`{A : Rep ℤ G}`, followed by:

```lean
def primeNormClass_eq_zero_exists_unit_norm_eqStatement
    (v : ValuationData D A)
    (K L S : FiniteAbstractField G)
    (hLK : L.field.toSubgroup ≤ K.field.toSubgroup)
    (hSK : S.field.toSubgroup ≤ K.field.toSubgroup)
    (hTot : (DegreeData.AbstractExtension.mk
      L.field K.field hLK).IsTotallyRamified D)
    [hLKfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field hLK)]
    [hSKfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S.field hSK)]
    (hSigmaResidue :
      ((DegreeData.FiniteAbstractExtension.ofInclusion
        S.field K.field hSK).residueDegree D : ℕ) = 1)
    (k : ℕ)
    (piS : ambientFixedAddSubgroup A S.field)
    (piL : ambientFixedAddSubgroup A L.field)
    (hpiS : v.IsPrimeElement S piS)
    (hpiL : v.IsPrimeElement L piL)
    (hclass :
      finiteNormClass A K.field L.field hLK
          (relativeNorm A K.field S.field hSK (k • piS)) = 0) : Prop :=
    ∃ w : v.unitAddSubgroup L,
      relativeNorm A K.field L.field hLK (k • piL + w.1) =
        relativeNorm A K.field S.field hSK (k • piS)
```

Let `L` and `S` (written `Σ` in the docstring) be finite over `K`, with
`L | K` totally ramified and `S | K` of relative residue degree one, and let
`π_S`, `π_L` be prime elements of `S` and `L`. If the norm from `S` of
`k π_S` has zero class in `A^{G_K} ⧸ N_{L|K} A^{G_L}`, then there is a
unit `w ∈ U_L` with `N_{L|K}(k π_L + w) = N_{S|K}(k π_S)` (additive
notation for `π_L^k w`).

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace `theorem primeNormClass_eq_zero_exists_unit_norm_eq … : statement := proof`
   by `def primeNormClass_eq_zero_exists_unit_norm_eqStatement … : Prop := statement`.
   The telescope and statement are copied verbatim. The source proof is
   omitted: this contribution publishes the proposition target, and its
   proof is separate work.
3. Prefix the source docstring with `Target:`, lower-case the first word
   after it and rewrap the lines; the wording is unchanged. Replace the
   source module docstring by a description of
   this module with a modification notice that names the source theorem.
4. Put `set_option linter.unusedVariables false in` before the target. The
   proposition does not mention the binders `hTot`, `hSigmaResidue`, `hpiS`,
   `hpiL` and `hclass`, and the linter would otherwise warn; the option
   changes no declaration.
5. Replace the source import by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions`
   (M039.006, which also brings M024.009 and M023.001),
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.NumericDefinitions`
   (M010.086, which also brings M010.002, M010.028, M010.045 and M010.068),
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Prime.Definitions`
   (M028.007 and M028.008, which also bring M025.012, M025.013, M025.025,
   M010.121, M008.008 and M002.001) and
   `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`
   (M004.002).
6. Omit the other declarations of the source file and the unused
   `open CategoryTheory`. Retain `open KummerTheory` (for
   `ambientFixedAddSubgroup`), `open CyclicCohomology` (for
   `extensionSubgroup`), the noncomputable section, the comment, both
   variable lines and the namespaces.
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
