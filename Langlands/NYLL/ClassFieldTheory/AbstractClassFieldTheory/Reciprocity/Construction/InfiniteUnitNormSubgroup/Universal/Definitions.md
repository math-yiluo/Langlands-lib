# NYLL M050.003: the universal unit norm group

The paired Lean file adapts the definition `ValuationData.infiniteUnitNormSubgroup` of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/InfiniteUnitNormSubgroup.lean`.
The pinned source file has SHA-256
`76dc70f70fa3f98c73692f48121a9ecf2f2d7b77d15716f857befe0368ce9ffd`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source definition after `ClassFormation.ValuationData.` | Docstring | Declaration | Adapted declaration |
| --- | --- | --- | --- | --- |
| M050.003 | `infiniteUnitNormSubgroup` | 101–102 | 103–108 | `Langlands.NYLL.ClassFormation.ValuationData.infiniteUnitNormSubgroup` |

The enclosing source context is `universe u` (line 17),
`namespace ClassFormation` (line 19), `open KummerTheory` (line 21),
`open CyclicCohomology` (line 22), `noncomputable section` (line 26),
`open CategoryTheory` (line 28), `open scoped BigOperators` (line 29), the
variables `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`
(line 31), `namespace ValuationData` (line 33) and the variables
`{D : DegreeData G} {A : Rep ℤ G}` (line 35). The only source import is
the unported module
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.InfiniteUnitDescent`
(line 7). The rest of the source file is not part of this module; the
statements M050.004 and M050.006 about this definition are in the sibling
module `Reciprocity.Construction.InfiniteUnitNormSubgroup.Universal.Statements`.

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
- `FiniteIntermediateField E K` (M029.001, from
  `Reciprocity.Construction.NormSubgroup.Definitions`), an intermediate
  field `E | M | K` finite over `K`;
- `ValuationData.finiteIntermediateUnitNormRange v E K M` (M050.001, from
  `Reciprocity.Construction.InfiniteUnitNormSubgroup.Definitions`), the
  additive subgroup `N_{M|K} U_M` of `A^{G_K}`: the range of the relative
  norm from `A^{G_M}` restricted to the units `U_M`;

`iInf` (`⨅`) of additive subgroups is Mathlib's.

## Definition

The definition has the binders implicit `{G : IntegralRepGroupType}`,
`[Group G]`, `[TopologicalSpace G]`, `{D : DegreeData G}` and
`{A : Rep ℤ G}`, followed by:

```lean
def infiniteUnitNormSubgroup
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G) :
    AddSubgroup (ambientFixedAddSubgroup A K.field) :=
  ⨅ M : FiniteIntermediateField E K.field,
    v.finiteIntermediateUnitNormRange E K M
```

The universal unit norm group `N_{E|K} U_E` of an extension `E | K`: the
intersection, over all finite intermediate fields `M`, of the unit norm
ranges `N_{M|K} U_M`, an additive subgroup of `A^{G_K}`.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace the source import by the published module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.InfiniteUnitNormSubgroup.Definitions`
   (M050.001, which also brings M029.001, M025.012, M023.001, M010.121,
   M010.002 and M002.001).
3. Replace the source module docstring by a description of this module with
   a modification notice that names the source definition.
4. Omit the rest of the source file, the unused `universe u` and the unused
   `open CyclicCohomology`, `open CategoryTheory` and
   `open scoped BigOperators`. Retain `open KummerTheory` (for
   `ambientFixedAddSubgroup`), the noncomputable section, both variable
   lines and the namespaces.
5. The binders, docstring and body are unchanged.

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
