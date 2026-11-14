# NYLL M141.001: the norm on the trivial value-group module

Worker 120, 14 November 2026.

## Statement and scope

This pair proves the published proposition
`Langlands.NYLL.LocalClassFieldTheory.galoisGroupValueGroup_tateNorm_toAddStatement`
under the required theorem name
`Langlands.NYLL.LocalClassFieldTheory.galoisGroupValueGroup_tateNorm_toAdd`.
The theorem's type is the target applied to all its parameters: the section
variables `K L : Type u` with `[Field K] [Field L] [Algebra K L]
[FiniteDimensional K L]`, then `a : Multiplicative ℤ`.
Its sole import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.ValueGroupCohomology.Statements`.
The published statement and its imported definitions remain unchanged.

The statement says that, with the trivial action
`galoisGroupValueGroupMulDistribMulAction K L` of `Gal(L/K)` on
`Multiplicative ℤ`,

```lean
Multiplicative.toAdd (tateNorm (Gal(L / K)) (Multiplicative Int) a) =
  (Fintype.card (Gal(L / K)) : Int) * Multiplicative.toAdd a
```

that is, the finite-group norm `∏ σ, σ • a` on the trivially acted-on value
group is multiplication by the order of the Galois group, written
additively.

## Implemented proof

```lean
  unfold galoisGroupValueGroup_tateNorm_toAddStatement
  let := galoisGroupValueGroupMulDistribMulAction K L
  have hsmul : ∀ (σ : Gal(L / K)) (n : Multiplicative Int), σ • n = n := by
    intro σ n
    rfl
  have hnorm : tateNorm (Gal(L / K)) (Multiplicative Int) a =
      a ^ Fintype.card (Gal(L / K)) := by
    simp only [tateNorm, hsmul, Finset.prod_const, Finset.card_univ]
  simpa only [toAdd_pow, nsmul_eq_mul] using
    congrArg Multiplicative.toAdd hnorm
```

The target definition is unfolded and the trivial action is put in the local
context, as in the source.

`hsmul` states that every Galois element acts trivially on
`Multiplicative ℤ`. This is NYLL M140.006
`galoisGroupValueGroupMulDistribMulAction_smul`. That proof is not yet in the
Library, so it is proved here by its original `rfl`: the published action's
`smul` is `fun _ n => n`.

`hnorm` unfolds the published `tateNorm` to the product
`∏ g : Gal(L/K), g • a`. `hsmul` turns each factor into `a`, so
`Finset.prod_const` and `Finset.card_univ` give `a ^ Fintype.card (Gal(L/K))`.
Applying `Multiplicative.toAdd` and simplifying with `toAdd_pow` and
`nsmul_eq_mul` turns `toAdd (a ^ n)` into `(n : ℤ) * toAdd a`, which is the
goal.

`hsmul` is a `have` inside the proof, so the file adds no declaration
besides the required theorem. The proof uses only the published definitions
reached through the statement import and Mathlib. It invokes no NYLL
theorem.

## Original source and modifications

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/ValueGroupCohomology.lean`,
lines 33–46 (docstring at lines 33–34, theorem at lines 35–46). The file's
SHA-256 is
`6ee54afe1a8a664d94bff689a3725f8fa4a92aa4054f0f371c7d199074ec59e9`.
The inlined M140.006 proof is from
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/Valuation.lean`
(SHA-256 `478460e530e2a37ae4dc4eaad7db80d4dfa290f5bdd715a66d507ab2539579e0`),
where it is `intro hValueAction; rfl` at lines 98–99.

| Source declaration | Published proof declaration |
| --- | --- |
| `LocalClassFieldTheory.galoisGroupValueGroup_tateNorm_toAdd` | `Langlands.NYLL.LocalClassFieldTheory.galoisGroupValueGroup_tateNorm_toAdd` |

Modifications: the namespace prefix `Langlands.NYLL`; the focused statement
import; the source section variables become explicit binders. The result is
expressed as the published target proposition applied to all its
parameters, so the proof first unfolds that definition. The source's
`simp only` lemma `galoisGroupValueGroupMulDistribMulAction_smul` (M140.006)
is replaced by the local fact `hsmul` with its original proof. The task
allows such local proofs and forbids publishing a second copy under the
adapted name. The source `noncomputable section`, the `open scoped
BigOperators` line and all other source declarations are omitted.

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

This support lemma proves M141.001 only. It does not publish M140.006, and it
proves no host class-formation, cup-product, transfer, Tate-cohomology or
reciprocity target.

## Development validation

Lean service check `5eb71dad-81e2-4397-956b-36f4785b57fa` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled the proof without errors or
warnings; the inspected theorem has level parameter `u` and assumptions
`propext`, `Classical.choice` and `Quot.sound` only. Independent review,
exact-target validation and publication remain separate.
