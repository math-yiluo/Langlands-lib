# NYLL M058.014: the additive order of a prime class in an unramified norm quotient

The paired Lean file adapts the statement of the theorem `primeClass_addOrderOf` of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UnramifiedNormQuotient.lean`.
The pinned source file has SHA-256
`66f9331ed7cc55c2f6726e4580486f0d4e1b6395d364313e77f5d8dbb17de1b6`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.ValuationData.` | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M058.014 | `primeClass_addOrderOf` | 390–392 | 393–403 | 403–459 | `Langlands.NYLL.ClassFormation.ValuationData.primeClass_addOrderOfStatement` |

The enclosing source context is `universe u` (line 21),
`namespace ClassFormation` (line 23), `open KummerTheory` (line 25),
`open CyclicCohomology` (line 27), `noncomputable section` (line 31),
`section valuationQuotient` (lines 152–488), the comment and variables
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` and
`{D : DegreeData G} {A : Rep ℤ G}` (lines 154–156) and
`namespace ValuationData` (lines 158–486). The source imports (lines 7–8)
are the modules `FiniteNormQuotient` and `ReciprocityIndependence` of
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction`.

The names used resolve to `Langlands.NYLL` declarations:

- `IntegralRepGroupType` (M002.001), the abbreviation `Type 0`, and
  `DegreeData` (M010.002);
- `ValuationData D A` (M025.012, from
  `Degree.Valuation.ValuationData.Definitions`), an additive valuation on
  the base-field fixed module of `A` with values in `ZHat`, with the value
  group `v.valueGroup : AddSubgroup ZHat` (M025.013) and
  `v.valueModulo n hn : v.valueGroup →+ ZMod n` (M025.016), reduction of
  values modulo `n` for `0 < n`;
- `ValuationData.valuationAt` (M025.025, from
  `Degree.Valuation.ValuationData.Normalized.Definitions`), the normalized
  valuation `A^{G_K} →+ v.valueGroup` of a finite abstract field `K`;
- `FiniteAbstractField` (M010.121) with its closed subgroup `K.field`;
- `FiniteAbstractFieldExtension.ofInclusion` (M010.131, from
  `Degree.Fields.FiniteAbstractField.Extension.OfInclusion`), which bundles
  a closed subgroup `L ≤ K.field` with finite quotient as a finite abstract
  field extension of `K`, and its degree
  `FiniteAbstractFieldExtension.degree` (M010.135), a positive natural
  number `[L : K]`;
- `KummerTheory.ambientFixedAddSubgroup` (M023.001), the fixed module
  `A^{G_K}`;
- `CyclicCohomology.extensionSubgroup` (M004.002), the abbreviation
  `L.toSubgroup.subgroupOf K.toSubgroup`.
- `DegreeData.AbstractExtension.mk L K.field hLK` (M010.028) and its
  predicate `IsUnramified D` (M010.044, from
  `Degree.Fields.AbstractExtension.StructuralDefinitions`):
  `G_K ⊓ ker d ≤ G_L`, where `d` is the degree map of `D`;
- `ValuationData.IsPrimeElement` (M028.007, from
  `Degree.PrimeElements.Prime.Definitions`): `π ∈ A^{G_K}` is prime when
  its normalized valuation at `K` is the distinguished value one;
- `FiniteNormQuotient A K L hLK` (M039.002) and `finiteNormClass` (M039.006,
  both from `Reciprocity.Construction.FiniteNormQuotient.Definitions`): the
  quotient `A^{G_K} ⧸ N_{L|K}(A^{G_L})` with its additive group
  instance, and the class of an element of `A^{G_K}` in it.

`addOrderOf` is Mathlib's.

## Target and complete telescope

The target has the binders implicit `{G : IntegralRepGroupType}`,
`[Group G]`, `[TopologicalSpace G]`, implicit `{D : DegreeData G}` and
implicit `{A : Rep ℤ G}`, followed by:

```lean
def primeClass_addOrderOfStatement
    (v : ValuationData D A)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D)
    (π : ambientFixedAddSubgroup A K.field) (hπ : v.IsPrimeElement K π) :
    Prop :=
    addOrderOf
      (finiteNormClass A K.field L hLK π) =
      ((FiniteAbstractFieldExtension.ofInclusion L K hLK).degree : ℕ)
```

For an unramified finite extension `L | K` and a prime element `π` of
`A^{G_K}`, the class of `π` in the norm quotient
`A^{G_K} ⧸ N_{L|K}(A^{G_L})` has additive order exactly `[L : K]`.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace `theorem primeClass_addOrderOf … : statement := proof` by
   `def primeClass_addOrderOfStatement … : Prop := statement`. The statement
   is copied verbatim. The source proof is omitted: this contribution
   publishes the proposition target, and its proof is separate work.
3. Prefix the source docstring with `Target:`. Replace the source module
   docstring by a description of this module with a modification notice
   that names the source theorem.
4. Put `set_option linter.unusedVariables false in` before the target. The
   proposition does not mention `hUnramified` and `hπ`, and the linter would
   otherwise warn; the option changes no declaration.
5. Replace the source imports by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions`
   (M039.002, M039.006),
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Prime.Definitions`
   (M028.007, which also brings M025.012 and M025.025),
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.StructuralDefinitions`
   (M010.044) and
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.OfInclusion`
   (M010.131, M010.135).
6. Omit the other declarations of the source file, the unused `universe u`
   and the section `valuationQuotient` (its comment and variable lines are
   kept). Retain both `open` lines, the noncomputable section and the
   namespaces.
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
