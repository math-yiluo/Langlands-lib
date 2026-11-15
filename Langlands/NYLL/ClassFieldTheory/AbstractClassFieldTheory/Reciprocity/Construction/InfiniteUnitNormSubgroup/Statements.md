# NYLL M050.002 and M050.005: unit norm ranges of finite intermediate fields

The paired Lean file adapts the statements of the theorems `ValuationData.mem_finiteIntermediateUnitNormRange_of_overfield` and `ValuationData.finiteIntermediateUnitNormRange_le_normRange` of Naganori
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

| Unit | Source theorem after `ClassFormation.ValuationData.` | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M050.002 | `mem_finiteIntermediateUnitNormRange_of_overfield` | 49–50 | 51–61 | 61–98 | `Langlands.NYLL.ClassFormation.ValuationData.mem_finiteIntermediateUnitNormRange_of_overfieldStatement` |
| M050.005 | `finiteIntermediateUnitNormRange_le_normRange` | 124–127 | 128–133 | 133–143 | `Langlands.NYLL.ClassFormation.ValuationData.finiteIntermediateUnitNormRange_le_normRangeStatement` |

The enclosing source context is `universe u` (line 17),
`namespace ClassFormation` (line 19), `open KummerTheory` (line 21),
`open CyclicCohomology` (line 22), `noncomputable section` (line 26),
`open CategoryTheory` (line 28), `open scoped BigOperators` (line 29), the
variables `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`
(line 31), `namespace ValuationData` (line 33) and the variables
`{D : DegreeData G} {A : Rep ℤ G}` (line 35). The only source import is
the unported module
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.InfiniteUnitDescent`
(line 7). The definition M050.001 of the same source file is in the
published sibling module
`Reciprocity.Construction.InfiniteUnitNormSubgroup.Definitions`; M050.003,
M050.004 and M050.006 are in
`Reciprocity.Construction.InfiniteUnitNormSubgroup.Universal`.

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
  `Reciprocity.Construction.NormSubgroup.Definitions`), a closed subgroup
  `M.field` with `M.above : E.toSubgroup ≤ M.field.toSubgroup`,
  `M.below : M.field.toSubgroup ≤ K.toSubgroup` and the finiteness `M.finite`
  of `K.toSubgroup ⧸ extensionSubgroup K M.field M.below`, an intermediate
  field `E | M | K` finite over `K`;
- `FiniteIntermediateField.toFiniteAbstractField K M` (M049.002, from
  `Reciprocity.Construction.InfiniteUnitDescent.Definitions`), `M` as a
  finite abstract field: the upper endpoint of
  `FiniteAbstractFieldExtension.ofInclusion M.field K M.below`, whose field
  is `M.field`;
- `ValuationData.unitAddSubgroup v K` (M028.008, from
  `Degree.PrimeElements.Prime.Definitions`), the kernel `U_K` of the
  normalized valuation `v_K` (M025.025) on `A^{G_K}`;
- `ValuationData.finiteIntermediateUnitNormRange v E K M` (M050.001, from
  `Reciprocity.Construction.InfiniteUnitNormSubgroup.Definitions`), the
  additive subgroup `N_{M|K} U_M` of `A^{G_K}`: the range of the relative
  norm from `A^{G_M}` restricted to the units `U_M`;
- `finiteIntermediateNormRange A E K M` (M029.003) and
  `infiniteNormSubgroup A E K` (M029.004, both from
  `Reciprocity.Construction.NormSubgroup.InfiniteNorm.Definitions`): the
  norm range `N_{M|K} A^{G_M}` of one finite intermediate field, and the
  universal norm group `⋂_M N_{M|K} A^{G_M}`;
- `CyclicCohomology.extensionSubgroup` (M004.002), the abbreviation
  `extensionSubgroup K L hLK = L.toSubgroup.subgroupOf K.toSubgroup`;
- `relativeNorm A K L hLK` (M024.009, from
  `Degree.Norm.RelativeNorm.Definitions`), the relative norm
  `A^{G_L} →+ A^{G_K}`, with the finiteness of `G_K ⧸ G_L` as instance
  argument, here `hPfinite`.

## Targets and complete telescopes

Both targets have the binders implicit `{G : IntegralRepGroupType}`,
`[Group G]`, `[TopologicalSpace G]`, `{D : DegreeData G}` and
`{A : Rep ℤ G}`, followed by those shown.

### M050.002

```lean
def mem_finiteIntermediateUnitNormRange_of_overfieldStatement
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (M P : FiniteIntermediateField E K.field)
    (hPM : P.field.toSubgroup ≤ M.field.toSubgroup)
    [hPfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below)]
    (uP : v.unitAddSubgroup (P.toFiniteAbstractField K))
    (aK : ambientFixedAddSubgroup A K.field)
    (haK : relativeNorm A K.field P.field P.below uP.1 = aK) : Prop :=
    aK ∈ v.finiteIntermediateUnitNormRange E K M
```

Let `M` and `P` be finite intermediate fields of `E | K` with `P` above `M`
(`G_P ≤ G_M`). If `aK ∈ A^{G_K}` is the norm from `P` of a unit
`uP ∈ U_P`, then `aK` lies in `N_{M|K} U_M`.

### M050.005

```lean
def finiteIntermediateUnitNormRange_le_normRangeStatement
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (M : FiniteIntermediateField E K.field) : Prop :=
    v.finiteIntermediateUnitNormRange E K M ≤
      finiteIntermediateNormRange A E K.field M
```

The unit norm range `N_{M|K} U_M` is contained in the norm range
`N_{M|K} A^{G_M}`.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. Each telescope and statement
   is copied verbatim. The source proofs are omitted: this contribution
   publishes the proposition targets, and their proofs are separate work.
3. Prefix each source docstring with `Target:`, lower-case the first word
   after it and rewrap the lines; the wording is unchanged. Replace the
   source module docstring by a description of this module with a
   modification notice that names the source theorems.
4. Put `set_option linter.unusedVariables false in` before the M050.002
   target. Its proposition does not mention the binders `hPM`, `hPfinite`
   and `haK`, and the linter would otherwise warn; the option changes no
   declaration.
5. Replace the source import by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.InfiniteUnitNormSubgroup.Definitions`
   (M050.001, which also brings M049.002, M029.001, M028.008, M025.012,
   M024.009, M023.001, M010.121, M010.002, M004.002 and M002.001) and
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.InfiniteNorm.Definitions`
   (M029.003 and M029.004).
6. Omit the other declarations of the source file, the unused `universe u`
   and the unused `open CategoryTheory` and `open scoped BigOperators`.
   Retain `open KummerTheory` (for `ambientFixedAddSubgroup`),
   `open CyclicCohomology` (for `extensionSubgroup`), the noncomputable
   section, both variable lines and the namespaces.
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
