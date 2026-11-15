# NYLL M033.001: the normal core field of a finite intermediate field

The paired Lean file adapts the definition `ClassFormation.FiniteIntermediateField.normalCoreField` of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean`.
The pinned source file has SHA-256
`169ddc13c58e7f6ef6ae39a433fb381c533464174c4245210c8bec5d69ffd5e4`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source definition after `ClassFormation.FiniteIntermediateField.` | Docstring | Declaration | Adapted declaration |
| --- | --- | --- | --- | --- |
| M033.001 | `normalCoreField` | 35–36 | 37–49 | `Langlands.NYLL.ClassFormation.FiniteIntermediateField.normalCoreField` |

The enclosing source context is `universe u` (line 17),
`namespace ClassFormation` (line 19), `open KummerTheory` (line 21),
`open CyclicCohomology` (line 23), `noncomputable section` (line 27),
`section groupTheoreticRefinements` (line 29), the variables
`{G : Type u} [Group G] [TopologicalSpace G]` (line 31) and
`namespace FiniteIntermediateField` (line 33). The source imports are the
unported modules
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom`
and
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityDefinition`
(lines 7–8). The rest of the source file is not part of this module. The
statements M033.002–.004 about this definition are in the sibling module
`Reciprocity.Construction.ReciprocityIndependence.NormalCoreField.Statements`;
M033.008–.010 are the published modules
`Reciprocity.Construction.ReciprocityIndependence.CompositumWith.{Definitions,Statements}`.

The names used resolve as follows:

- `FiniteIntermediateField E K` (M029.001, from
  `Reciprocity.Construction.NormSubgroup.Definitions`), a structure with a
  closed subgroup `M.field`, `M.above : E.toSubgroup ≤ M.field.toSubgroup`,
  `M.below : M.field.toSubgroup ≤ K.toSubgroup` and the finiteness
  `M.finite` of `K.toSubgroup ⧸ extensionSubgroup K M.field M.below`: an
  intermediate field `E | M | K` finite over `K`;
- `CyclicCohomology.extensionSubgroup K L hLK` (M004.002, from
  `GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`), the
  abbreviation `L.toSubgroup.subgroupOf K.toSubgroup`, that is `G_L` as a
  subgroup of `G_K`;
- `KummerTheory.extensionSubgroup_isClosed K L hLK` (M020.008, the published
  theorem of
  `GaloisCohomology.Kummer.Abstract.KummerAbelianCyclicFactors.U008.Proofs`),
  whose type is the published target
  `extensionSubgroup_isClosedStatement K L hLK`, by definition
  `IsClosed (extensionSubgroup K L hLK : Set K.toSubgroup)`: `G_L` is closed
  in `G_K`.

`ClosedSubgroup`, `IsTopologicalGroup`, `Subgroup.normalCore`,
`Subgroup.map`, `Subgroup.subtype`, `Subgroup.normalCore_isClosed`,
`IsClosed.isClosedEmbedding_subtypeVal` and
`Topology.IsClosedEmbedding.isClosedMap` are Mathlib's.

## Definition

The definition has the binders implicit `{G : Type u}`, `[Group G]` and
`[TopologicalSpace G]`, followed by:

```lean
def normalCoreField [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K) :
    ClosedSubgroup G where
  toSubgroup :=
    (extensionSubgroup K M.field M.below).normalCore.map
      K.toSubgroup.subtype
  isClosed' := by
    change IsClosed
      (Subtype.val ''
        ((extensionSubgroup K M.field M.below).normalCore : Set K.toSubgroup))
    exact K.isClosed'.isClosedEmbedding_subtypeVal.isClosedMap _
      ((extensionSubgroup K M.field M.below).normalCore_isClosed
        (extensionSubgroup_isClosed K M.field M.below))
```

For a finite intermediate field `E | M | K`, the normal core of `G_M` inside
`G_K` (the largest subgroup of `G_M` normal in `G_K`), mapped back into `G`
by the inclusion of `G_K`. It is closed because the normal core of the
closed subgroup `G_M` of `G_K` is closed and `G_K` is closed in `G`. Under
the contravariant correspondence between fields and closed subgroups, this
intersection of the `G_K`-conjugates of `G_M` corresponds to the Galois
closure of `M` over `K`; the Lean definition is the subgroup itself.

The field `isClosed'` is a proof. Through `extensionSubgroup_isClosed`
(M020.008) it uses a published theorem; the definition contains no
unproved assumption.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above. `open KummerTheory` resolves `extensionSubgroup_isClosed`
   and `open CyclicCohomology` resolves `extensionSubgroup`.
2. Replace the source imports by the published modules
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Definitions`
   (M029.001, which also brings M004.002) and
   `Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianCyclicFactors.U008.Proofs`
   (M020.008).
3. Replace the source module docstring by a description of this module with
   a modification notice that names the source definition.
4. Omit the rest of the source file. Retain `universe u`, both opens, the
   noncomputable section, the section `groupTheoreticRefinements`, its
   variable line and the namespaces.
5. The binders, docstring and body are unchanged.

No helper declaration or instance is added. This definition discharges no
host class-formation, cup, transfer, Tate or reciprocity target.

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
