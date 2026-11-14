# NYLL M026.006: membership in the absolute extension subgroup

`Langlands.NYLL.PortInternal.M026.d006` proves the published proposition
`Langlands.NYLL.PortInternal.M026.d006Statement` of module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Statements`. It is the port
of the private source theorem `ClassFormation.mem_absoluteExtension`; private
source declarations receive `Langlands.NYLL.PortInternal` names in this port.

## Statement

The parameters are, in order, implicit `G : Type u_1`, instances `[Group G]` and
`[TopologicalSpace G]`, and explicit `K : ClosedSubgroup G` and
`x : (baseField G).toSubgroup`. The type of the theorem is exactly
`Langlands.NYLL.PortInternal.M026.d006Statement K x`, which unfolds to

```lean
x ∈ extensionSubgroup (baseField G) K (le_baseField K) ↔ x.1 ∈ K
```

Here `baseField G` (M010.003) is the closed subgroup `⊤` and `le_baseField K` is
the published M010.005. An element of the absolute subgroup lies in the relative
subgroup of `K` over the base field exactly when its underlying element lies in
`K`.

## Implemented proof

The proof is the unchanged source term `Iff.rfl`. Both sides are definitionally
the same proposition: `extensionSubgroup (baseField G) K _` is the `abbrev`
`K.toSubgroup.subgroupOf (baseField G).toSubgroup`, and Mathlib defines membership
in `H.subgroupOf K'` as membership of the coercion `(x : G)` in `H`, which is
`x.1 ∈ K`. The expected type `d006Statement K x` is a definition that the
elaborator unfolds when checking `Iff.rfl`, so no `show` or `intro` is needed.

The only direct import is `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Statements`, which transitively supplies `baseField`,
`le_baseField` and `extensionSubgroup`. The theorem is declared inside the
namespace `Langlands.NYLL.ClassFormation` (so that `baseField` resolves) with a
`_root_` prefix, exactly like its target. The kernel axioms reported by
inspection are `propext`, `Classical.choice` and `Quot.sound`; they enter through
the imported definitions in the statement type, not through the proof term.

## Source correspondence and modifications

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, pinned
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean`, SHA-256
`985cb864c6b3360e38bf22dbea58d22685eb1146537166fcc8f5ca89821dd44f`, retained
under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Its registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

Unit M026.006 is the private theorem `ClassFormation.mem_absoluteExtension`:
statement lines 105–109 and proof line 110; it has no docstring. Worker 5014
extracts it into this focused module, makes it public under the port-internal name
`Langlands.NYLL.PortInternal.M026.d006` (the name required by the task, matching
the target `...d006Statement`), replaces the source imports by the published
statement module, writes the conclusion as the published target applied to the
parameters, and adds a docstring identifying the source theorem. The parameter
telescope and the proof term are the source ones.

This is an abstract subgroup-level fact of the NYLL abstract-field model. It
discharges no host class-formation, cup, transfer, Tate or reciprocity target.

## Attribution

The original copyright, author and Apache-2.0 header is retained verbatim, and
the Lean module docstring records the modifications. The existing Library files
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are preserved unchanged; their
SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
