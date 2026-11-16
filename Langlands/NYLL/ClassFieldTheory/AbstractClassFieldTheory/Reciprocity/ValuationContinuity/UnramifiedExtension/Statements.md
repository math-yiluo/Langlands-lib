# Targets M301.006–.007: membership in and inclusion of the degree-`f` unramified subgroup

This file states two theorems of Naganori Yamaguchi's
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean`
as Prop-valued targets. The source is pinned at commit
`fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`, and the original file SHA-256 is
`29a3ec39fcabc17faa969f1c4c225a7cfd07555a00298e58daaa4b6fa6c7bb60`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

| Unit | Source lines (declaration line) | Original theorem | Adapted target |
| --- | --- | --- | --- |
| M301.006 | 85–96 (90) | `ClassFormation.DegreeData.mem_unramifiedExtensionOfDegree_iff` | `Langlands.NYLL.ClassFormation.DegreeData.mem_unramifiedExtensionOfDegree_iffStatement` |
| M301.007 | 98–105 (99) | `ClassFormation.DegreeData.unramifiedExtensionOfDegree_le` | `Langlands.NYLL.ClassFormation.DegreeData.unramifiedExtensionOfDegree_leStatement` |

Both targets are about the published M301.005 closed subgroup
`unramifiedExtensionOfDegree D K f hf : ClosedSubgroup G`. That subgroup is
the image in `G` of the kernel `unramifiedDegreeKernelWithin D K f hf` of
reduction modulo `f` after the normalized degree `d_K` on `K.toSubgroup`.
See the paired Markdown of the definition module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ValuationContinuity.UnramifiedExtension.Definitions`.

## Telescopes

Both targets keep the source universe `u` and section variables
`{G : Type u} [Group G] [TopologicalSpace G]` (source lines 30 and 34). After
these they take, in source order, the explicit `(D : DegreeData G)`, the
instance binder `[IsTopologicalGroup G]` and the explicit
`(K : FiniteResidueAbstractField D) (f : ℕ) (hf : 0 < f)`. M301.006 also takes
the explicit `(g : G)`. No hypothesis is added or removed.

## M301.006: membership

```lean
def mem_unramifiedExtensionOfDegree_iffStatement (D : DegreeData G)
    [IsTopologicalGroup G] (K : FiniteResidueAbstractField D)
    (f : ℕ) (hf : 0 < f) (g : G) : Prop :=
  g ∈ unramifiedExtensionOfDegree D K f hf ↔
    ∃ k : K.toSubgroup,
      k ∈ unramifiedDegreeKernelWithin D K f hf ∧ k.1 = g
```

An element `g : G` lies in the closed subgroup exactly when some element `k`
of `K.toSubgroup` lies in the reduction kernel `unramifiedDegreeKernelWithin D K f hf`
and has underlying element `k.1 = g`. Membership on the left is the
`SetLike` membership of Mathlib's `ClosedSubgroup`. The right side is the
existential over the actual subgroup `K.toSubgroup`, with the defining kernel
of M301.002 and the specified underlying element `g`. In the source the
proof is `Iff.rfl`, so this is the unfolded definition of `Subgroup.map`
membership.

## M301.007: inclusion

```lean
def unramifiedExtensionOfDegree_leStatement (D : DegreeData G)
    [IsTopologicalGroup G] (K : FiniteResidueAbstractField D)
    (f : ℕ) (hf : 0 < f) : Prop :=
  (unramifiedExtensionOfDegree D K f hf).toSubgroup ≤
    K.toSubgroup
```

The underlying subgroup of the unramified closed subgroup is contained in
`K.toSubgroup`, i.e. `G_L ≤ G_K`. This is the order of `Subgroup G`. The
statement is the inclusion hypothesis taken by `extensionSubgroup` and by
`FiniteGaloisSubextension.below`. In the source, the theorem
`unramifiedExtensionOfDegree_le` that proves it is passed as this inclusion
argument in M301.008 and M301.010.

## Modifications

Worker 452 makes these modifications:

- Turn each source theorem into a Prop-valued `def` with the source name plus
  the suffix `Statement`. The binders, binder kinds and proposition are
  unchanged. The proofs (`Iff.rfl` for M301.006, and
  `rintro g ⟨k, _, rfl⟩; exact k.2` for M301.007) are omitted. They are
  separate proof units.
- Omit the source `@[simp]` attribute (line 89) of M301.006. In the source it
  makes the proved equivalence a rewrite rule. On a Prop-valued definition it
  would only make `simp` unfold the definition, so it belongs to the eventual
  proof unit.
- Prefix the source namespace `ClassFormation` with `Langlands.NYLL`. Retain
  the source noncomputable section, `open scoped Topology`, the section
  `DegreeOnly` and the namespace `DegreeData`. Omit the unused
  `open ClassFormation CyclicCohomology KummerTheory`. Omit all other source
  declarations.
- Replace the source imports by the single published module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ValuationContinuity.UnramifiedExtension.Definitions`
  (M301.005). It transitively supplies M301.001/.002 and the field data.
- The M301.008 target is not in this module. Its source type uses the
  M301.007 proof term, which exists only after this target has been proved,
  so Task 6082 submits it later as a separate target.
- Retain the original copyright, Apache-2.0 and author header. The Lean
  module documentation adds an explicit modification record.

The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
