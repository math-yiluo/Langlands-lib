# NYLL M014.022: the relative inertia subgroup is closed

The paired Lean file adapts the statement of one theorem of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean`.
The pinned source file has SHA-256
`cda9dddf5f551fc8c81de825093b52cba99d644e45eb274682d2ee986585bfe3`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.DegreeData.` | Docstring | Telescope and statement | Proof | Adapted target after `Langlands.NYLL.ClassFormation.DegreeData.` |
| --- | --- | --- | --- | --- | --- |
| M014.022 | `extensionInertiaWithin_isClosed` | 446 | 447–451 | 451–464 | `extensionInertiaWithin_isClosedStatement` |

The source context is `namespace ClassFormation` (line 19),
`open CyclicCohomology` (line 21), `noncomputable section` (line 25),
`universe u` (line 27), the variables
`{G : Type u} [Group G] [TopologicalSpace G]` (line 29) and
`namespace DegreeData` (line 300). The source imports are the NYLL modules
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift`,
`Nyll.GaloisCohomology.ProfiniteIntegers.TopologicalGeneration` and
`Nyll.GaloisCohomology.Topology.TotallyDisconnectedQuotients` (lines 7–9).
The other declarations of the source file are outside this contribution.

The statement uses these published declarations:

- `DegreeData G` (M010.002, from `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`), the
  degree datum: a continuous homomorphism `degree : G →ₜ* ZHatMul`, where
  `ZHatMul` is `Multiplicative ZHat`, with `degree_surjective`;
- `DegreeData.FiniteResidueAbstractField D` (M010.021, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.Definitions`), a structure with a closed
  subgroup `K.field : ClosedSubgroup G` and the finiteness of the residue
  quotient `D.residueQuotient K.field`: an abstract field with finite
  residue degree;
- `D.extensionInertiaWithin K L hLK` (M012.002, from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.Definitions`), the subgroup
  `L.toSubgroup.subgroupOf K.toSubgroup ⊓ D.fieldInertiaWithin K` of
  `K.toSubgroup`, where `D.fieldInertiaWithin K` (M010.014) is the kernel of
  the restricted degree `D.restrictedDegree K` (M010.008) on `G_K`; that is
  the inertia subgroup `I_L` of `L`, viewed inside `G_K`;
- Mathlib's `ClosedSubgroup G`, with its underlying subgroup
  `K.toSubgroup` and the subspace topology on `K.toSubgroup`.

The module imports `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.Definitions` and
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.Definitions`.

## Target and complete telescope

The target has, before the binders shown, the binders of the source
variable line 29: implicit `{G : Type u}` and the instances `[Group G]`
and `[TopologicalSpace G]`.

```lean
def extensionInertiaWithin_isClosedStatement (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) : Prop :=
    IsClosed (D.extensionInertiaWithin K.field L hLK : Set K.field.toSubgroup)
```

For a degree datum `D` on a topological group `G`, an abstract field `K`
with finite residue degree and a closed subgroup `L` contained in
`G_K = K.field.toSubgroup`, the relative inertia subgroup
`D.extensionInertiaWithin K.field L hLK` is a closed subset of `G_K`. The
source proof writes it as the intersection of
`extensionSubgroup K.field L hLK`, closed because `L` is closed, with the
kernel of the continuous restricted degree.

The hypothesis `hLK` is used by the proposition, so no linter option is
needed. The source proof of M017.002 `extensionImageInInertiaQuotient_isClosed`
uses this theorem.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the target lies in
   `Langlands.NYLL.ClassFormation.DegreeData`.
2. Replace `theorem extensionInertiaWithin_isClosed … : statement := proof`
   by `def extensionInertiaWithin_isClosedStatement … : Prop := statement`.
   The telescope and the statement are copied verbatim, including the
   binder names, kinds and order. The source proof is omitted: this
   contribution publishes the proposition target, and its proof is
   separate work.
3. Prefix the source docstring with `Target:` and lower-case the first word
   after it; the wording is otherwise unchanged, and the line is rewrapped.
   Replace the source module docstring by a description of this module with
   a modification notice.
4. Replace the source imports by the two focused published imports above.
5. Keep the namespaces, the noncomputable section, `universe u` and the
   variable line 29; omit `open CyclicCohomology`, which the statement does
   not use, and the rest of the source file.
6. No helper declaration, instance or linter option is added.

This is the exact source statement as a named proposition, without a
published proof. It discharges no host class-formation, cup, transfer, Tate or reciprocity
target.

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
