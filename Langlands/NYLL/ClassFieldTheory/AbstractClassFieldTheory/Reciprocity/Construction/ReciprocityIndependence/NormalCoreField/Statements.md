# NYLL M033.002–.004: the normal core field lies below `K` and `M` and represents the normal core

The paired Lean file adapts the statements of the theorems `ClassFormation.FiniteIntermediateField.normalCoreField_le`, `normalCoreField_le_field` and `extensionSubgroup_normalCoreField` of Naganori
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

| Unit | Source theorem after `ClassFormation.FiniteIntermediateField.` | Docstring | Telescope and statement | Proof | Adapted target |
| --- | --- | --- | --- | --- | --- |
| M033.002 | `normalCoreField_le` | 51 | 52–54 | 54–56 | `Langlands.NYLL.ClassFormation.FiniteIntermediateField.normalCoreField_leStatement` |
| M033.003 | `normalCoreField_le_field` | 58 | 59–61 | 61–64 | `Langlands.NYLL.ClassFormation.FiniteIntermediateField.normalCoreField_le_fieldStatement` |
| M033.004 | `extensionSubgroup_normalCoreField` | 66 | 67–70 | 70–80 | `Langlands.NYLL.ClassFormation.FiniteIntermediateField.extensionSubgroup_normalCoreFieldStatement` |

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
(lines 7–8). The definition M033.001 `normalCoreField` of the same source file is
in the sibling module
`Reciprocity.Construction.ReciprocityIndependence.NormalCoreField.Definitions`.
The rest of the source file is not part of this module.

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
- `FiniteIntermediateField.normalCoreField M` (M033.001, from the sibling
  module `Reciprocity.Construction.ReciprocityIndependence.NormalCoreField.Definitions`),
  the closed subgroup of `G` obtained by mapping the normal core of
  `extensionSubgroup K M.field M.below` in `G_K` into `G`.

`ClosedSubgroup`, `IsTopologicalGroup` and `Subgroup.normalCore` are
Mathlib's.

## Targets and complete telescopes

All three targets have the binders implicit `{G : Type u}`, `[Group G]` and
`[TopologicalSpace G]`, followed by those shown.

### M033.002

```lean
def normalCoreField_leStatement [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K) : Prop :=
  (M.normalCoreField).toSubgroup ≤ K.toSubgroup
```

The normal core field lies below `K`: `G_core ≤ G_K`.

### M033.003

```lean
def normalCoreField_le_fieldStatement [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K) : Prop :=
  (M.normalCoreField).toSubgroup ≤ M.field.toSubgroup
```

The normal core field lies below `M`: `G_core ≤ G_M`.

### M033.004

```lean
def extensionSubgroup_normalCoreFieldStatement [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K) : Prop :=
  extensionSubgroup K M.normalCoreField
      (show (M.normalCoreField).toSubgroup ≤ K.toSubgroup by
        rintro g ⟨k, _, rfl⟩
        exact k.2) =
    (extensionSubgroup K M.field M.below).normalCore
```

The normal core field, as a subgroup of `G_K`, is the normal core of `G_M`
in `G_K`.

The source statement is
`extensionSubgroup K M.normalCoreField M.normalCoreField_le = (extensionSubgroup K M.field M.below).normalCore`.
Its third argument `M.normalCoreField_le` is the proof of M033.002, which is
not yet published. The target writes the source proof of M033.002
(lines 55–56, `rintro g ⟨k, _, rfl⟩` then `exact k.2`) inline as a term of
the same type `(M.normalCoreField).toSubgroup ≤ K.toSubgroup`. The third
argument of `extensionSubgroup` is a proof of a proposition, so by proof
irrelevance the target is the same proposition as the source statement,
whatever proof of M033.002 is published later.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. The telescopes and the
   statements of M033.002 and M033.003 are copied verbatim; in M033.004 the
   proof term `M.normalCoreField_le` is replaced by the inline source proof,
   as explained above. The source proofs are omitted: this contribution
   publishes the proposition targets, and their proofs are separate work.
3. Prefix each source docstring with `Target:`, lower-case the first word
   after it and rewrap the lines; the wording is unchanged. Replace the
   source module docstring by a description of this module with a
   modification notice that names the source theorems.
4. Replace the source imports by the published sibling module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence.NormalCoreField.Definitions`
   (M033.001, which also brings M029.001 and M004.002).
5. Omit the other declarations of the source file and the unused
   `open KummerTheory`. Retain `universe u`, `open CyclicCohomology` (for
   `extensionSubgroup`), the noncomputable section, the section
   `groupTheoreticRefinements`, its variable line and the namespaces. Every
   binder occurs in its proposition, so no linter option is needed.
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
