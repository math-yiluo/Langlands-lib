# NYLL M301.006–.007: membership and inclusion of the unramified subgroup

This module proves the two published targets
`Langlands.NYLL.ClassFormation.DegreeData.mem_unramifiedExtensionOfDegree_iffStatement`
and
`Langlands.NYLL.ClassFormation.DegreeData.unramifiedExtensionOfDegree_leStatement`
from the sibling `UnramifiedExtension.Statements` module. It exports the
source names `mem_unramifiedExtensionOfDegree_iff` and
`unramifiedExtensionOfDegree_le` in the namespace
`Langlands.NYLL.ClassFormation.DegreeData`.

## Source and attribution

The proofs are adapted from Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean`.
The source file SHA-256 is
`29a3ec39fcabc17faa969f1c4c225a7cfd07555a00298e58daaa4b6fa6c7bb60`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the supplemental registration is `nyll-classfieldtheory-fbd320cd-supplement`.
The readable original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

| Unit | Original lines (declaration line) | Exported theorem |
| --- | --- | --- |
| M301.006 | 85–96 (90), with `@[simp]` at 89 | `Langlands.NYLL.ClassFormation.DegreeData.mem_unramifiedExtensionOfDegree_iff` |
| M301.007 | 98–105 (99) | `Langlands.NYLL.ClassFormation.DegreeData.unramifiedExtensionOfDegree_le` |

The original copyright, Apache-2.0 license and author header are retained.
The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are used
unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Objects and hypotheses

The group `G : Type u` has a group structure, topology and
`IsTopologicalGroup G`. The degree datum `D : DegreeData G` and the
finite-residue abstract field `K : FiniteResidueAbstractField D` are the
published NYLL objects. For `f : ℕ` and `hf : 0 < f`, the actual closed
subgroup `unramifiedExtensionOfDegree D K f hf` has underlying subgroup

```lean
(unramifiedDegreeKernelWithin D K f hf).map K.toSubgroup.subtype
```

Here `unramifiedDegreeKernelWithin D K f hf : Subgroup K.toSubgroup` is the
kernel of reduction modulo `f` after the normalized degree, and
`K.toSubgroup.subtype : K.toSubgroup →* G` is the subgroup inclusion.

Both theorem telescopes retain the source universe `u` (line 30), implicit
`{G : Type u} [Group G] [TopologicalSpace G]` (line 34), then explicit
`(D : DegreeData G)`, instance `[IsTopologicalGroup G]`, and explicit
`(K : FiniteResidueAbstractField D) (f : ℕ) (hf : 0 < f)` in that order.
The membership theorem also has the explicit final parameter `(g : G)`.
No compactness or class-field axiom is required.

## Implemented proofs

The membership theorem has type
`mem_unramifiedExtensionOfDegree_iffStatement D K f hf g`, which unfolds to

```lean
g ∈ unramifiedExtensionOfDegree D K f hf ↔
  ∃ k : K.toSubgroup,
    k ∈ unramifiedDegreeKernelWithin D K f hf ∧ k.1 = g
```

The proof is the source term `Iff.rfl`: membership in the subgroup image
is definitionally the existential on the right. The source `@[simp]`
attribute is retained on this proved equivalence.

The inclusion theorem has type
`unramifiedExtensionOfDegree_leStatement D K f hf`, which unfolds to

```lean
(unramifiedExtensionOfDegree D K f hf).toSubgroup ≤ K.toSubgroup
```

The source proof `rintro g ⟨k, _, rfl⟩; exact k.2` unpacks membership in
the subgroup image. Its witness `k : K.toSubgroup` already carries the
proof `k.2` that its underlying element is in `K.toSubgroup`. Substitution
of the witness equality closes the desired inclusion. The exported name
and full telescope permit later statements to use this exact inclusion term.

## Modifications

Worker 499 extracts only M301.006–.007 and retains both proof bodies.
The namespace is prefixed by `Langlands.NYLL`, and the source imports are
replaced by the single published `UnramifiedExtension.Statements` module,
which supplies the original subgroup definition transitively. Each result
type is written as the corresponding published Statement applied to the
same complete source telescope; it unfolds to the original proposition.
The source noncomputable section, topology scope, universe and `DegreeOnly`
section are retained. The unused source namespace openings and other source
declarations are omitted. Docstrings and module documentation describe
this focused proof unit.
