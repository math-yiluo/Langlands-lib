# Target M301.008: the extension subgroup of the degree-`f` unramified extension

This file states one theorem of Naganori Yamaguchi's
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean`
as a Prop-valued target. The source is pinned at commit
`fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`, and the original file SHA-256 is
`29a3ec39fcabc17faa969f1c4c225a7cfd07555a00298e58daaa4b6fa6c7bb60`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

| Unit | Source lines (declaration line) | Original theorem | Adapted target |
| --- | --- | --- | --- |
| M301.008 | 107–126 (111) | `ClassFormation.DegreeData.extensionSubgroup_unramifiedExtensionOfDegree` | `Langlands.NYLL.ClassFormation.DegreeData.extensionSubgroup_unramifiedExtensionOfDegreeStatement` |

## Telescope

The target keeps the source universe `u` and section variables
`{G : Type u} [Group G] [TopologicalSpace G]` (source lines 30 and 34). After
these it takes, in source order, the explicit `(D : DegreeData G)`, the
instance binder `[IsTopologicalGroup G]` and the explicit
`(K : FiniteResidueAbstractField D) (f : ℕ) (hf : 0 < f)`. No hypothesis is
added or removed.

## Statement

```lean
def extensionSubgroup_unramifiedExtensionOfDegreeStatement (D : DegreeData G)
    [IsTopologicalGroup G] (K : FiniteResidueAbstractField D)
    (f : ℕ) (hf : 0 < f) : Prop :=
  extensionSubgroup K.field (unramifiedExtensionOfDegree D K f hf)
      (unramifiedExtensionOfDegree_le D K f hf) =
    unramifiedDegreeKernelWithin D K f hf
```

The objects are the actual published ones:

- `extensionSubgroup` is
  `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002), opened from
  `CyclicCohomology` as in source line 28. For closed subgroups `K L` of `G`
  and `hLK : L.toSubgroup ≤ K.toSubgroup` it is
  `L.toSubgroup.subgroupOf K.toSubgroup : Subgroup K.toSubgroup`, i.e. `G_L`
  regarded as a subgroup of `G_K`.
- `unramifiedExtensionOfDegree D K f hf` is the M301.005 closed subgroup, and
  the inclusion argument is the M301.007 proof
  `Langlands.NYLL.ClassFormation.DegreeData.unramifiedExtensionOfDegree_le D K f hf`,
  used by name as in source line 115. It proves the published target
  `unramifiedExtensionOfDegree_leStatement D K f hf`, which unfolds to the
  required inclusion.
- `unramifiedDegreeKernelWithin D K f hf : Subgroup K.toSubgroup` is the
  M301.002 kernel of reduction modulo `f` after the normalized degree.

The equation says that the closed subgroup of the unramified extension,
pulled back into `K.toSubgroup` (where `K.toSubgroup` unfolds to
`K.field.toSubgroup`), is exactly the defining reduction kernel. Both sides
are subgroups of the same actual group `K.field.toSubgroup`. The equation
compares two different constructions, the image-then-restriction on the left
and the kernel on the right, so it is not reflexive.

## Modifications

Worker 452 makes these modifications:

- Turn the source theorem into a Prop-valued `def` with the source name plus
  the suffix `Statement`. The binders, binder kinds, proof argument and
  equation are unchanged. The source proof (lines 117–126) is omitted, since
  it is a separate proof unit.
- State this target in its own module rather than beside the M301.006/.007
  targets. Its source type contains the M301.007 proof term, which is
  available only after the M301.007 target has been published and proved.
- Prefix the source namespace `ClassFormation` with `Langlands.NYLL`. Retain
  the source noncomputable section, `open scoped Topology`, the section
  `DegreeOnly` and the namespace `DegreeData`. Of the source line
  `open ClassFormation CyclicCohomology KummerTheory`, retain only
  `open CyclicCohomology`, which supplies `extensionSubgroup`. The other two
  are unused here.
- Replace the source imports by two published modules. The first is
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ValuationContinuity.UnramifiedExtension.Proofs`,
  the module of the M301.006/.007 proofs. It supplies
  `unramifiedExtensionOfDegree_le` and transitively the M301.001/.002/.005
  objects and the M301.007 target `unramifiedExtensionOfDegree_leStatement`.
  The second is
  `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`,
  which supplies `extensionSubgroup`.
- Retain the original copyright, Apache-2.0 and author header. The Lean
  module documentation adds an explicit modification record.

The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
