# NYLL M058.008: finite norms lie in the kernel of the unramified valuation map

The paired Lean file adapts the statement of the private theorem `ValuationData.finiteNormSubgroup_le_unramifiedValuationHom_ker` of Naganori
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
| M058.008 | `finiteNormSubgroup_le_unramifiedValuationHom_ker` (private) | none | 195–203 | 203–221 | `Langlands.NYLL.PortInternal.M058.d008Statement` |

The enclosing source context is `universe u` (line 21),
`namespace ClassFormation` (line 23), `open KummerTheory` (line 25),
`open CyclicCohomology` (line 27), `noncomputable section` (line 31),
`section valuationQuotient` (from line 152), the comment and variables
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` and
`{D : DegreeData G} {A : Rep ℤ G}` (lines 154–156) and
`namespace ValuationData` (from line 158). The source imports (lines 7–8)
are the unported modules `FiniteNormQuotient` and `ReciprocityIndependence`
of `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction`.

The source theorem is private, so the port follows the convention of the
published sibling module
`Reciprocity.Construction.UnramifiedNormQuotient.ValuationHom.Definitions`,
which exposes the private source definition `unramifiedValuationHom`
(M058.007) as `Langlands.NYLL.PortInternal.M058.d007`: the target of
M058.008 is `Langlands.NYLL.PortInternal.M058.d008Statement` in the same
namespace, and its eventual proof is `Langlands.NYLL.PortInternal.M058.d008`.

The names used resolve to `Langlands.NYLL` declarations:

- `IntegralRepGroupType` (M002.001, from
  `GaloisCohomology.Cyclic.IntegralRepUniverse`), the abbreviation `Type 0`;
- `DegreeData G` (M010.002, from `Degree.Fields.Definitions`), a continuous
  surjective degree homomorphism `G →ₜ* ZHatMul`;
- `ValuationData D A` (M025.012, from
  `Degree.Valuation.ValuationData.Definitions`), a henselian valuation of the
  base-field fixed module;
- `FiniteAbstractField G` (M010.121, from
  `Degree.Fields.FiniteAbstractField.Definitions`), a closed subgroup
  `K.field` of finite index over the base field;
- `KummerTheory.ambientFixedAddSubgroup A H` (M023.001, from
  `GaloisCohomology.Kummer.Abstract.KummerDelta.U001.Definitions`), the
  additive subgroup `A^H` of elements of `A` fixed by `H`;
- `Langlands.NYLL.PortInternal.M058.d007 v K L hLK` (M058.007, from
  `Reciprocity.Construction.UnramifiedNormQuotient.ValuationHom.Definitions`),
  the source's `v.unramifiedValuationHom K L hLK`: the normalized valuation
  `v_K` on `A^{G_K}` followed by reduction modulo the degree `[L : K]`, an
  additive homomorphism into `ZMod [L : K]`;
- `finiteNormSubgroup A K L hLK` (M039.001, from
  `Reciprocity.Construction.FiniteNormQuotient.Definitions`), the range
  `N_{L|K} A^{G_L}` of the relative norm, with the finiteness of
  `G_K ⧸ G_L` as instance argument;
- `CyclicCohomology.extensionSubgroup` (M004.002), the abbreviation
  `extensionSubgroup K L hLK = L.toSubgroup.subgroupOf K.toSubgroup`;
- `DegreeData.AbstractExtension.mk L K.field hLK` (the constructor of
  M010.028) and `DegreeData.AbstractExtension.IsUnramified` (M010.044, from
  `Degree.Fields.AbstractExtension.StructuralDefinitions`):
  `E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ E.field.toSubgroup`, the
  inertia of the base lies in the field.

`AddMonoidHom.ker` and the order on additive subgroups are Mathlib's.

## Target and complete telescope

The target has the binders implicit `{G : IntegralRepGroupType}`,
`[Group G]`, `[TopologicalSpace G]`, `{D : DegreeData G}` and
`{A : Rep ℤ G}`, followed by:

```lean
def d008Statement
    (v : ValuationData D A)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) : Prop :=
    finiteNormSubgroup A K.field L hLK ≤
      (d007 v K L hLK).ker
```

For an unramified finite extension `L | K`, every norm `N_{L|K} a` lies in
the kernel of `v_K` reduced modulo `[L : K]`, that is, its normalized
valuation is divisible by `[L : K]`.

## Modifications

Worker 5264 made these changes:

1. Replace `private theorem finiteNormSubgroup_le_unramifiedValuationHom_ker … : statement := proof`
   by `def d008Statement … : Prop := statement` in the namespace
   `Langlands.NYLL.PortInternal.M058` (with `open ClassFormation`), and
   replace `v.unramifiedValuationHom K L hLK` by the published
   `d007 v K L hLK`. The telescope and the rest of the statement are copied
   verbatim. The source proof is omitted: this contribution publishes the
   proposition target, and its proof is separate work.
2. Add a docstring, which the source theorem lacks; it describes the
   proposition. Replace the source module docstring by a description of
   this module with a modification notice that names the source theorem.
3. Put `set_option linter.unusedVariables false in` before the target. The
   proposition does not mention the binder `hUnramified`, and the linter
   would otherwise warn; the option changes no declaration.
4. Replace the source imports by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnramifiedNormQuotient.ValuationHom.Definitions`
   (M058.007, which also brings M004.002, M025.012, M010.121, M023.001 and
   M002.001),
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions`
   (M039.001) and
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.StructuralDefinitions`
   (M010.044, which also brings M010.002 and M010.028).
5. Omit the other declarations of the source file and the section
   `valuationQuotient` (its comment and variable lines are kept). Retain
   `open KummerTheory`, `open CyclicCohomology` and the noncomputable section.
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
