# NYLL M058.007: the valuation homomorphism modulo an extension degree

The paired Lean file adapts the private definition `unramifiedValuationHom` of Naganori
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

| Unit | Source definition after `ClassFormation.ValuationData.` | Docstring | Declaration | Adapted declaration |
| --- | --- | --- | --- | --- |
| M058.007 | `private def unramifiedValuationHom` | none | 183–193 | `Langlands.NYLL.PortInternal.M058.d007` |

The enclosing source context is `universe u` (line 21),
`namespace ClassFormation` (line 23), `open KummerTheory` (line 25),
`open CyclicCohomology` (line 27), `noncomputable section` (line 31),
`section valuationQuotient` (lines 152–488), the comment and variables
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` and
`{D : DegreeData G} {A : Rep ℤ G}` (lines 154–156) and
`namespace ValuationData` (lines 158–486). The source imports (lines 7–8)
are the modules `FiniteNormQuotient` and `ReciprocityIndependence` of
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction`. The rest of the source file is not part of this module.

The source definition is private, so the port exposes it as
`Langlands.NYLL.PortInternal.M058.d007`. A source call
`v.unramifiedValuationHom K L hLK` corresponds to
`PortInternal.M058.d007 v K L hLK`. The source uses it in the private
theorem M058.008 and in the definition M058.009
`unramifiedNormQuotientValuation` and the statement of M058.010, which are
not part of this contribution.

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

`AddMonoidHom.comp`, `ZMod`, `ℕ+` and `Subtype.property` are Mathlib's.

## Definition

The definition has the binders implicit `{G : IntegralRepGroupType}`,
`[Group G]`, `[TopologicalSpace G]`, implicit `{D : DegreeData G}` and
implicit `{A : Rep ℤ G}`, followed by:

```lean
def d007
    (v : ValuationData D A) (K : FiniteAbstractField G)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    ambientFixedAddSubgroup A K.field →+
      ZMod ((FiniteAbstractFieldExtension.ofInclusion L K hLK).degree : ℕ) :=
  (v.valueModulo
      ((FiniteAbstractFieldExtension.ofInclusion L K hLK).degree : ℕ)
      (FiniteAbstractFieldExtension.ofInclusion L K hLK).degree.property).comp
    (v.valuationAt K)
```

For valuation data `v`, a finite abstract field `K` and a finite extension
`L | K`, the additive map `A^{G_K} → ℤ/nℤ` with `n = [L : K]`: the
normalized valuation at `K` followed by reduction modulo `n`.

## Modifications

Worker 5264 made these changes:

1. Expose the private source definition as
   `Langlands.NYLL.PortInternal.M058.d007`, declared in
   `namespace Langlands.NYLL.PortInternal.M058` with `open ClassFormation`;
   source references resolve to the names above.
2. Add a docstring (the source definition has none).
3. Replace the source imports by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Normalized.Definitions`
   (M025.025, which also brings M002.001, M010.002, M010.121, M023.001,
   M025.012, M025.013 and M025.016),
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.OfInclusion`
   (M010.131, which also brings M010.135) and
   `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`
   (M004.002).
4. Replace the source module docstring by a description of this module with
   a modification notice that names the source definition.
5. Omit the rest of the source file, the unused `universe u` and the
   section `valuationQuotient` (its comment and variable lines are kept).
   Retain `open KummerTheory` (for `ambientFixedAddSubgroup`),
   `open CyclicCohomology` (for `extensionSubgroup`) and the noncomputable
   section.
6. The binders and body are unchanged.

No helper declaration or instance is added. This definition discharges
no host class-formation, cup, transfer, Tate or reciprocity target.

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
