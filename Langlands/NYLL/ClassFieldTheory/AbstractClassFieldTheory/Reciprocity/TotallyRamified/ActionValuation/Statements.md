# NYLL M083.003: normalized valuation is invariant under the quotient action

The paired Lean file adapts the statement of the theorem `ValuationData.valuationAt_extensionFixedRepresentation_action` of Naganori
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
| M083.003 | `valuationAt_extensionFixedRepresentation_action` | 198–200 | 201–217 | 217–235 | `Langlands.NYLL.ClassFormation.ValuationData.valuationAt_extensionFixedRepresentation_actionStatement` |

The enclosing source context is `namespace ClassFormation` (lines 27–444),
`open KummerTheory` (line 29), `open CyclicCohomology` (line 31),
`noncomputable section` (lines 35–443), `open CategoryTheory` (line 37), the
comment and variables `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`
(lines 39–40), `namespace ValuationData` (lines 89–441) and the variables
`{D : DegreeData G} {A : Rep ℤ G}` (line 91). The only source import is the
unported module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core`
(line 7). The rest of the source file is not part of this module; the target
of M083.002 is in the sibling module
`Reciprocity.TotallyRamified.PrimeNormUnit.Statements`.

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
- `FiniteAbstractFieldExtension G` (M010.130, from
  `Degree.Fields.FiniteAbstractField.Extension.Definitions`), two finite
  abstract fields `E.field` (the top field `L`) and `E.base` (the base field
  `K`) with `E.below : E.field.field.toSubgroup ≤ E.base.field.toSubgroup`
  and a finite relative quotient;
- `CyclicCohomology.extensionSubgroup` (M004.002, from
  `GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`), the
  abbreviation `extensionSubgroup K L hLK = L.toSubgroup.subgroupOf K.toSubgroup`;
- `CyclicCohomology.extensionFixedRepresentation A K L hLK hnormal` (M004.003,
  same module), the representation of `G_K ⧸ G_L` on the `G_L`-fixed vectors
  of `A` restricted to `G_K`;
- `extensionFixedRepresentationEquiv A K L hLK hnormal` (M073.001, from
  `Reciprocity.FieldRepresentation.FixedCarrier.Definitions`), the additive
  equivalence between the carrier of that representation and `A^{G_L}`.

`Rep ℤ G`, `Rep.V` and `Rep.ρ` are Mathlib's.

## Target and complete telescope

The target has the binders implicit `{G : IntegralRepGroupType}`,
`[Group G]`, `[TopologicalSpace G]`, `{D : DegreeData G}` and
`{A : Rep ℤ G}`, followed by:

```lean
def valuationAt_extensionFixedRepresentation_actionStatement
    (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup
      E.base.field E.field.field E.below).Normal)
    (q : E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
    (a : (extensionFixedRepresentation A E.base.field E.field.field
      E.below hnormal).V) : Prop :=
    v.valuationAt E.field
        (extensionFixedRepresentationEquiv A E.base.field E.field.field
          E.below hnormal
          ((extensionFixedRepresentation A E.base.field E.field.field
            E.below hnormal).ρ q a)) =
      v.valuationAt E.field
        (extensionFixedRepresentationEquiv A E.base.field E.field.field
          E.below hnormal a)
```

For a finite extension `L | K` (`L = E.field`, `K = E.base`) with `G_L`
normal in `G_K`, an element `q` of `G_K ⧸ G_L` and a vector `a` of the
descended representation, the normalized valuation `v_L` of `q · a`, read
in `A^{G_L}`, equals `v_L` of `a`.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace `theorem valuationAt_extensionFixedRepresentation_action … : statement := proof`
   by `def valuationAt_extensionFixedRepresentation_actionStatement … : Prop := statement`.
   The telescope and statement are copied verbatim. The source proof is
   omitted: this contribution publishes the proposition target, and its
   proof is separate work.
3. Prefix the source docstring with `Target:`, lower-case the first word
   after it and rewrap the lines; the wording is unchanged. Replace the
   source module docstring by a description of
   this module with a modification notice that names the source theorem.
4. Replace the source import by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FieldRepresentation.FixedCarrier.Definitions`
   (M073.001, which also brings M004.002, M004.003 and M023.001),
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.Definitions`
   (M010.130, which also brings M010.002 and M010.121) and
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Normalized.Definitions`
   (M025.025, which also brings M025.012, M025.013, M008.008 and M002.001).
5. Omit the other declarations of the source file and the unused
   `open KummerTheory` and `open CategoryTheory`. Retain
   `open CyclicCohomology` (for `extensionSubgroup` and
   `extensionFixedRepresentation`), the noncomputable section, the comment,
   both variable lines and the namespaces. Every binder of the target occurs
   in its proposition, so no linter option is needed.
6. No helper declaration or instance is added.

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
