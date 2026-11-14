# NYLL M140.013: surjectivity of the multiplicative normalized valuation

Worker 120, 14 November 2026.

## Statement and scope

This pair proves the published proposition
`Langlands.NYLL.LocalClassFieldTheory.valuationUnitsMulHom_surjectiveStatement`
under the required theorem name
`Langlands.NYLL.LocalClassFieldTheory.valuationUnitsMulHom_surjective`.
The theorem's type is the target applied to all its parameters: a field `L`
in universe `u` with a valuative relation, a topology and the
`IsNonarchimedeanLocalField L` instance.
The imports are the statement module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.Statements`
and the published proof module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U005.Proofs`.
The published statement and its imported definitions remain unchanged.

The statement is

```lean
Function.Surjective (valuationUnitsMulHom L)
```

that is, every element of `Multiplicative ℤ` is the multiplicative normalized
valuation of some field unit of `L`.

## Implemented proof

```lean
  unfold valuationUnitsMulHom_surjectiveStatement
  intro n
  rcases valuationMap_surjective L (Multiplicative.toAdd n) with ⟨x, hx⟩
  refine ⟨Additive.toMul x, ?_⟩
  change Multiplicative.ofAdd (valuationMap L x) = n
  rw [hx]
  rfl
```

The target definition is unfolded and `n : Multiplicative ℤ` is introduced.
The published theorem
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_surjective`
(NYLL M134.005, from the imported `ValuationExactSequence.U005.Proofs`
module) gives `x : Additive Lˣ` with
`valuationMap L x = Multiplicative.toAdd n`. The witness is the field unit
`Additive.toMul x`. Since the published `valuationMap L` is
`MonoidHom.toAdditive (valuationUnitsMulHom L)`, the goal
`valuationUnitsMulHom L (Additive.toMul x) = n` is definitionally
`Multiplicative.ofAdd (valuationMap L x) = n`, which `change` states. After
rewriting with `hx`, the goal `Multiplicative.ofAdd (Multiplicative.toAdd n) = n`
holds by `rfl`.

Besides the published definitions reached through the statement import, the
proof uses only M134.005 and Mathlib.

## Original source and modifications

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/Valuation.lean`,
lines 251–262 (docstring at lines 251–252, theorem at lines 253–262). The
file's SHA-256 is
`478460e530e2a37ae4dc4eaad7db80d4dfa290f5bdd715a66d507ab2539579e0`.
The source proof is the proof above without the initial `unfold`.

| Source declaration | Published proof declaration |
| --- | --- |
| `LocalClassFieldTheory.valuationUnitsMulHom_surjective` | `Langlands.NYLL.LocalClassFieldTheory.valuationUnitsMulHom_surjective` |

Modifications: the namespace prefix `Langlands.NYLL`; the focused statement
import plus the published `ValuationExactSequence.U005.Proofs` import, which
provides the source's `valuationMap_surjective`; the result is expressed as
the published target proposition applied to all its parameters, so the proof
first unfolds that definition. The source `noncomputable section` and all
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

This support lemma proves M140.013 only. It proves no host class-formation,
cup-product, transfer, Tate-cohomology or reciprocity target.

## Development validation

Lean service check `c3c42df0-6a3f-465b-94dd-5b3bf48e3cae` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled the proof without errors or
warnings; the inspected theorem has level parameter `u` and assumptions
`propext`, `Classical.choice` and `Quot.sound` only. Independent review,
exact-target validation and publication remain separate.
