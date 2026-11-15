# NYLL M033.006: a Galois refinement lies below the original finite field

The paired Lean file adapts the statement of the theorem `ClassFormation.FiniteIntermediateField.galoisRefinement_le_field` of Naganori
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
| M033.006 | `galoisRefinement_le_field` | 113 | 114–118 | 118–119 | `Langlands.NYLL.ClassFormation.FiniteIntermediateField.galoisRefinement_le_fieldStatement` |

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
(lines 7–8). The definition M033.005 `galoisRefinement` and the instance
M033.007 `galoisRefinement_normal` are in the sibling module
`Reciprocity.Construction.ReciprocityIndependence.GaloisRefinement.Definitions`.
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
- `FiniteIntermediateField.galoisRefinement M` (M033.005, from the sibling
  module `Reciprocity.Construction.ReciprocityIndependence.GaloisRefinement.Definitions`),
  the finite intermediate field of `E | K` whose closed subgroup is the
  normal core field `M.normalCoreField` (M033.001), defined when
  `extensionSubgroup K E (M.above.trans M.below)` is normal.

`ClosedSubgroup`, `IsTopologicalGroup` and `Subgroup.Normal` are Mathlib's.

## Target and complete telescope

The target has the binders implicit `{G : Type u}`, `[Group G]` and
`[TopologicalSpace G]`, followed by those shown:

```lean
def galoisRefinement_le_fieldStatement [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    [_hEnormal :
      (extensionSubgroup K E (M.above.trans M.below)).Normal] : Prop :=
  (M.galoisRefinement).field.toSubgroup ≤ M.field.toSubgroup
```

When `G_E` is normal in `G_K`, the closed subgroup of the Galois refinement
of `M` lies in `G_M`: the Galois closure of `M` over `K` contains `M`. The
telescope and the statement are the source's verbatim; the instance binder
`[_hEnormal : …]` is needed so that `M.galoisRefinement` elaborates.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`; source references resolve to
   the names above.
2. Replace `theorem galoisRefinement_le_field … : statement := proof` by
   `def galoisRefinement_le_fieldStatement … : Prop := statement`. The
   telescope and the statement are copied verbatim. The source proof
   `M.normalCoreField_le_field` (M033.003) is omitted: this contribution
   publishes the proposition target, and its proof is separate work.
3. Prefix the source docstring with `Target:` and lower-case the first word
   after it; the wording is otherwise unchanged. Replace the source module
   docstring by a description of this module with a modification notice
   that names the source theorem.
4. Replace the source imports by the sibling module
   `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence.GaloisRefinement.Definitions`
   of this contribution (M033.005, which also brings M033.001, M029.001
   and M004.002).
5. Omit the other declarations of the source file and the unused
   `open KummerTheory`. Retain `universe u`, `open CyclicCohomology` (for
   `extensionSubgroup`), the noncomputable section, the section
   `groupTheoreticRefinements`, its variable line and the namespaces. The
   source binder name `_hEnormal` already marks the binder as unused, so no
   linter option is needed.
6. No helper declaration or instance is added.

This is the exact source statement as a named proposition, without a
published proof. It discharges no host class-formation, cup, transfer,
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
