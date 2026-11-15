# NYLL M050.004 and M050.006: membership in the universal unit norm group

The paired Lean file adapts the statements of the theorems `ValuationData.mem_infiniteUnitNormSubgroup_iff` and `ValuationData.infiniteUnitNormSubgroup_le_normSubgroup` of Naganori
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

| Unit | Source theorem after `ClassFormation.ValuationData.` | Docstring | Attribute | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- | --- |
| M050.004 | `mem_infiniteUnitNormSubgroup_iff` | 110–113 | 114 (`@[simp]`) | 115–121 | 121–122 | `Langlands.NYLL.ClassFormation.ValuationData.mem_infiniteUnitNormSubgroup_iffStatement` |
| M050.006 | `infiniteUnitNormSubgroup_le_normSubgroup` | 146 | none | 147–150 | 150–155 | `Langlands.NYLL.ClassFormation.ValuationData.infiniteUnitNormSubgroup_le_normSubgroupStatement` |

The enclosing source context is `universe u` (line 17),
`namespace ClassFormation` (line 19), `open KummerTheory` (line 21),
`open CyclicCohomology` (line 22), `noncomputable section` (line 26),
`open CategoryTheory` (line 28), `open scoped BigOperators` (line 29), the
variables `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`
(line 31), `namespace ValuationData` (line 33) and the variables
`{D : DegreeData G} {A : Rep ℤ G}` (line 35). The only source import is
the unported module
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.InfiniteUnitDescent`
(line 7). The rest of the source file is not part of this module.

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
- `FiniteIntermediateField E K` (M029.001), an intermediate field
  `E | M | K` finite over `K`;
- `ValuationData.finiteIntermediateUnitNormRange v E K M` (M050.001, from
  `Reciprocity.Construction.InfiniteUnitNormSubgroup.Definitions`), the
  additive subgroup `N_{M|K} U_M` of `A^{G_K}`: the range of the relative
  norm from `A^{G_M}` restricted to the units `U_M`;
- `ValuationData.infiniteUnitNormSubgroup v E K` (M050.003, from the sibling
  module `Reciprocity.Construction.InfiniteUnitNormSubgroup.Universal.Definitions`),
  the intersection of the `N_{M|K} U_M` over all `M`;
- `infiniteNormSubgroup A E K` (M029.004, from
  `Reciprocity.Construction.NormSubgroup.InfiniteNorm.Definitions`), the
  universal norm group `⋂_M N_{M|K} A^{G_M}`.

## Targets and complete telescopes

Both targets have the binders implicit `{G : IntegralRepGroupType}`,
`[Group G]`, `[TopologicalSpace G]`, `{D : DegreeData G}` and
`{A : Rep ℤ G}`, followed by those shown.

### M050.004

```lean
def mem_infiniteUnitNormSubgroup_iffStatement
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A K.field) : Prop :=
    a ∈ v.infiniteUnitNormSubgroup E K ↔
      ∀ M : FiniteIntermediateField E K.field,
        a ∈ v.finiteIntermediateUnitNormRange E K M
```

An element lies in the universal unit norm group exactly when it lies in
every unit norm range `N_{M|K} U_M`.

### M050.006

```lean
def infiniteUnitNormSubgroup_le_normSubgroupStatement
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G) : Prop :=
    v.infiniteUnitNormSubgroup E K ≤ infiniteNormSubgroup A E K.field
```

The universal unit norm group is contained in the universal norm group.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. Each telescope and statement
   is copied verbatim. The `@[simp]` attribute of M050.004 is omitted: a
   definition of a proposition is not a rewriting lemma, and the attribute
   belongs on the eventual proof. The source proofs are omitted: this
   contribution publishes the proposition targets, and their proofs are
   separate work.
3. Prefix each source docstring with `Target:`, lower-case the first word
   after it and rewrap the lines; the wording is unchanged. Replace the
   source module docstring by a description of this module with a
   modification notice that names the source theorems.
4. Replace the source import by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.InfiniteUnitNormSubgroup.Universal.Definitions`
   (M050.003, which also brings M050.001, M029.001, M025.012, M023.001,
   M010.121, M010.002 and M002.001) and
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.InfiniteNorm.Definitions`
   (M029.004).
5. Omit the other declarations of the source file, the unused `universe u`
   and the unused `open CyclicCohomology`, `open CategoryTheory` and
   `open scoped BigOperators`. Retain `open KummerTheory` (for
   `ambientFixedAddSubgroup`), the noncomputable section, both variable
   lines and the namespaces. Every binder occurs in its proposition, so no
   linter option is needed.
6. No helper declaration or instance is added.

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
