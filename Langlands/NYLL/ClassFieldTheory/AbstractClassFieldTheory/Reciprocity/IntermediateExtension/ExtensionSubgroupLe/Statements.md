# NYLL M076.003: `G_L` lies in every intermediate subgroup

The paired Lean file adapts the statement of the theorem `extensionSubgroup_le_intermediateSubgroup` of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean`.
The pinned source file has SHA-256
`f031b91cd496accfb520a0665cbb59f5f8a4ac0f567ee2c5a5dffc408ef05b44`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.FiniteGaloisSubextension.` | `omit` | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- | --- |
| M076.003 | `extensionSubgroup_le_intermediateSubgroup` | 57 | 58 | 59–61 | 61–67 | `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.extensionSubgroup_le_intermediateSubgroupStatement` |

The enclosing source context is `namespace ClassFormation` (line 26),
`open KummerTheory` (line 28), `open CyclicCohomology` (line 30),
`noncomputable section` (line 34), the variables
`{G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]`
(line 36), `namespace FiniteGaloisSubextension` (line 38) and
`variable {K : ClosedSubgroup G}` (line 40). Line 57 is
`omit [IsTopologicalGroup G] in`, so the source theorem does not take the
topological-group instance.

The names used in the statement resolve to `Langlands.NYLL` declarations:

- `FiniteGaloisSubextension K` (M040.001, from
  `Reciprocity.FiniteGaloisSubextension.Definitions`), a finite Galois
  extension `L` of the closed subgroup `K`, with fields `L.field` (the
  closed subgroup `G_L`) and `L.below : L.field.toSubgroup ≤ K.toSubgroup`;
- `FiniteGaloisSubextension.extensionQuotient` (M040.004, same module), the
  quotient `G(L/K) = G_K ⧸ G_L`, with the group instance M040.008;
- `CyclicCohomology.extensionSubgroup` (M004.002, from
  `GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`), the
  abbreviation `extensionSubgroup K L hLK = L.toSubgroup.subgroupOf K.toSubgroup`,
  i.e. `G_L` viewed as a subgroup of `G_K`;
- `FiniteGaloisSubextension.intermediateSubgroup` (M076.001, from
  `Reciprocity.IntermediateExtension.Definitions`), the inverse image in
  `G_K` of a subgroup `S ≤ G(L/K)` under the quotient map.

`ClosedSubgroup`, `Subgroup` and its order are Mathlib's.

## Target and complete telescope

The target has the binders implicit `{G : Type u_1}`, `[Group G]`,
`[TopologicalSpace G]` and implicit `{K : ClosedSubgroup G}`, followed by:

```lean
def extensionSubgroup_le_intermediateSubgroupStatement
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) : Prop :=
    extensionSubgroup K L.field L.below ≤ L.intermediateSubgroup S
```

For a finite Galois extension `L | K` and any subgroup `S` of
`G(L/K) = G_K ⧸ G_L`, the subgroup `G_L` of `G_K` is contained in the
inverse image of `S` in `G_K`.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace `theorem extensionSubgroup_le_intermediateSubgroup … : statement := proof`
   by `def extensionSubgroup_le_intermediateSubgroupStatement … : Prop := statement`.
   The statement is copied verbatim. The source proof is omitted: this
   contribution publishes the proposition target, and its proof is separate
   work.
3. Prefix the source docstring with `Target:`. Replace the source module
   docstring by a description of this module with a modification notice
   that names the source theorem.
4. Write the section variable line without `[IsTopologicalGroup G]` instead
   of the source line 36 followed by `omit [IsTopologicalGroup G] in`; the
   resulting binders are the same.
5. Replace the source imports by the published module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension.Definitions`
   (M076.001, which also brings M040.001, M040.004 and M004.002).
6. Omit `open KummerTheory`, which the statement does not use. Retain
   `open CyclicCohomology` (for `extensionSubgroup`), the noncomputable
   section and the namespaces.
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
