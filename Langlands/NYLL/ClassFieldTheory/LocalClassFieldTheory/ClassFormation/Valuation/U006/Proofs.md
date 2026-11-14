# NYLL M140.006: the Galois action on the value group is trivial

Worker 120, 14 November 2026.

## Statement and scope

This pair proves the published proposition
`Langlands.NYLL.LocalClassFieldTheory.galoisGroupValueGroupMulDistribMulAction_smulStatement`
under the required theorem name
`Langlands.NYLL.LocalClassFieldTheory.galoisGroupValueGroupMulDistribMulAction_smul`.
The theorem's type is the target applied to all its parameters:
fields `K` and `L` in one universe `u`, a `K`-algebra structure on `L`, a
Galois automorphism `σ : Gal(L/K)` and `n : Multiplicative ℤ`.
Its sole import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.Statements`.
The published statement and its imported definitions remain unchanged.

The statement says that under the local action
`galoisGroupValueGroupMulDistribMulAction K L` on `Multiplicative ℤ`,
`σ • n = n`.

## Implemented proof

```lean
  unfold galoisGroupValueGroupMulDistribMulAction_smulStatement
  intro hValueAction
  rfl
```

The target definition is unfolded so that its local action binder can be
introduced. The published action
`galoisGroupValueGroupMulDistribMulAction K L` (in
`ClassFormation.Valuation.Definitions`) has scalar multiplication field
`smul _ n := n`, so `σ • n` reduces to `n` and `rfl` closes the goal.
No other NYLL theorem is used.

## Original source and modifications

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/Valuation.lean`,
lines 90–99 (docstring at line 90, `@[simp]` at line 91, theorem at
lines 92–99). The file's SHA-256 is
`478460e530e2a37ae4dc4eaad7db80d4dfa290f5bdd715a66d507ab2539579e0`.
The source proof is `intro hValueAction; rfl`.

| Source declaration | Published proof declaration |
| --- | --- |
| `LocalClassFieldTheory.galoisGroupValueGroupMulDistribMulAction_smul` | `Langlands.NYLL.LocalClassFieldTheory.galoisGroupValueGroupMulDistribMulAction_smul` |

Modifications: the namespace prefix `Langlands.NYLL`; the focused statement
import; the result is expressed as the published target proposition applied
to all its parameters, so the proof first unfolds that definition; the
theorem-only `@[simp]` attribute, the source `noncomputable section` and all
other source declarations are omitted.

The retained original snapshot is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Registered sources are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

The original copyright, Apache-2.0 license statement and author header are
preserved in the Lean file, followed by the modification record. The
inherited `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain
unchanged, with SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This support lemma proves M140.006 only. It proves no host class-formation,
cup-product, transfer, Tate-cohomology or reciprocity target.

## Development validation

Lean service check `7e05771f-3833-4895-8b0a-f4d7d4f73695` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled the proof without errors or
warnings; the inspected theorem has level parameter `u` and assumptions
`propext` and `Quot.sound` only. Independent review, exact-target validation
and publication remain separate.
