# NYLL M141.003: reduction modulo the Galois order is surjective

Worker 120, 14 November 2026.

## Statement and scope

This pair proves the published proposition
`Langlands.NYLL.LocalClassFieldTheory.galoisGroupValueGroupFixedToZModHom_surjectiveStatement`
under the required theorem name
`Langlands.NYLL.LocalClassFieldTheory.galoisGroupValueGroupFixedToZModHom_surjective`.
The theorem's type is the target applied to all its parameters: the section
variables `K L : Type u` with `[Field K] [Field L] [Algebra K L]
[FiniteDimensional K L]`.
Its sole import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.ValueGroupCohomology.Statements`.
The published statement and its imported definitions remain unchanged.

The statement says that, with the trivial action
`galoisGroupValueGroupMulDistribMulAction K L` of `Gal(L/K)` on
`Multiplicative ℤ`,

```lean
Function.Surjective (galoisGroupValueGroupFixedToZModHom K L)
```

where the published `galoisGroupValueGroupFixedToZModHom K L` is the
reduction map from the fixed subgroup
`fixedSubgroup (Gal(L / K)) (Multiplicative Int)` to
`Multiplicative (ZMod (Fintype.card (Gal(L / K))))`. It is built as
`(Int.castAddHom _).toMultiplicative` composed with the subgroup inclusion.

## Implemented proof

```lean
  unfold galoisGroupValueGroupFixedToZModHom_surjectiveStatement
  let := galoisGroupValueGroupMulDistribMulAction K L
  intro y
  rcases ZMod.intCast_surjective (Multiplicative.toAdd y) with ⟨z, hz⟩
  let x : fixedSubgroup (Gal(L / K)) (Multiplicative Int) :=
    ⟨Multiplicative.ofAdd z, by intro σ; rfl⟩
  refine ⟨x, ?_⟩
  rw [show galoisGroupValueGroupFixedToZModHom K L x =
      Multiplicative.ofAdd
        ((z : Int) : ZMod (Fintype.card (Gal(L / K)))) by rfl]
  exact congrArg Multiplicative.ofAdd hz
```

The target definition is unfolded, the trivial action is put in the local
context, and a target element `y` is introduced. Mathlib's
`ZMod.intCast_surjective` gives an integer `z` whose cast is
`Multiplicative.toAdd y`. The preimage is `x = Multiplicative.ofAdd z`. It
lies in the fixed subgroup because the published action's `smul` is
`fun _ n => n`, so `σ • x = x` holds by `rfl` for every `σ`. The image of `x`
is by definition `Multiplicative.ofAdd ((z : ℤ) : ZMod _)`, which the `show
… by rfl` rewrite records. Applying `Multiplicative.ofAdd` to `hz` then gives
`Multiplicative.ofAdd (Multiplicative.toAdd y)`, that is, `y`.

The proof uses only the published definitions reached through the statement
import and Mathlib's `ZMod.intCast_surjective`. It invokes no NYLL theorem.

## Original source and modifications

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/ValueGroupCohomology.lean`,
lines 59–72 (docstring at line 59, theorem at lines 60–72). The file's
SHA-256 is
`6ee54afe1a8a664d94bff689a3725f8fa4a92aa4054f0f371c7d199074ec59e9`.
The source proof is the proof above without the initial `unfold`.

| Source declaration | Published proof declaration |
| --- | --- |
| `LocalClassFieldTheory.galoisGroupValueGroupFixedToZModHom_surjective` | `Langlands.NYLL.LocalClassFieldTheory.galoisGroupValueGroupFixedToZModHom_surjective` |

Modifications: the namespace prefix `Langlands.NYLL`; the focused statement
import; the source section variables become explicit binders. The result is
expressed as the published target proposition applied to all its
parameters, so the proof first unfolds that definition and then runs the
source proof unchanged. The source docstring, which only restates the
theorem's name, is replaced by a descriptive one. The source `noncomputable
section`, the `open scoped BigOperators` line and all other source
declarations are omitted.

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

This support lemma proves M141.003 only. It proves no host class-formation,
cup-product, transfer, Tate-cohomology or reciprocity target.

## Development validation

Lean service check `99ebeaeb-b87f-4e12-a8f6-996544eee2fc` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled the proof without errors or
warnings; the inspected theorem has level parameter `u` and assumptions
`propext`, `Classical.choice` and `Quot.sound` only. Independent review,
exact-target validation and publication remain separate.
