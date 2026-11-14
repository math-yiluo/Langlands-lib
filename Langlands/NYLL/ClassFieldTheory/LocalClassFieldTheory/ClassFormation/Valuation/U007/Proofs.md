# NYLL M140.007: equivariance of the inclusion of integer units

Worker 120, 14 November 2026.

## Statement and scope

This pair proves the published proposition
`Langlands.NYLL.LocalClassFieldTheory.integerUnitsToFieldUnits_galoisGroup_equivariantStatement`
under the required theorem name
`Langlands.NYLL.LocalClassFieldTheory.integerUnitsToFieldUnits_galoisGroup_equivariant`.
The theorem's type is the target applied to all its parameters:
fields `K` and `L` in one universe `u` with valuative relations, a
`K`-algebra structure on `L`, the valuation-extension instance, the
integral-closure instance `IsIntegralClosure 𝒪[L] 𝒪[K] L`, a Galois
automorphism `σ : Gal(L/K)` and an integer unit `x : 𝒪[L]ˣ`.
The imports are the statement module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.IntegerStatements`
and the published proof module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing.Proofs`.
The published statement and its imported definitions remain unchanged.

The statement says that, with the integral-closure action
`galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L` on
`𝒪[L]ˣ` and the canonical action `galoisGroupFieldUnitsMulDistribMulAction K L`
on `Lˣ`,

```lean
integerUnitsToFieldUnits L (σ • x) = σ • integerUnitsToFieldUnits L x
```

that is, the inclusion `𝒪[L]ˣ → Lˣ` commutes with the two Galois actions.

## Implemented proof

```lean
  unfold integerUnitsToFieldUnits_galoisGroup_equivariantStatement
  intro hIntegerAction hFieldAction
  ext
  change
    ((galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (x : 𝒪[L]) : 𝒪[L]) : L) =
      σ ((x : 𝒪[L]) : L)
  exact galoisGroupIntegerRingEquivOfIsIntegralClosure_apply K L σ (x : 𝒪[L])
```

The target definition is unfolded so that its two local action binders can
be introduced. `ext` reduces the equality in `Lˣ` to the equality of the
underlying elements of `L`. The published `integerUnitsToFieldUnits L` is
`Units.map` of the inclusion `𝒪[L] → L`; the integer-unit action is
`Units.mulDistribMulActionRight` over the compHom semiring action whose
underlying map is `galoisGroupIntegerRingEquivOfIsIntegralClosure K L`; and
the field-unit action is Mathlib's action of `Gal(L/K)` on `Lˣ`. So the left
side is definitionally the ambient value of
`galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x` and the right side is
`σ` applied to the ambient value of `x`; `change` states this form.

The published theorem
`Langlands.NYLL.LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure_apply`
(NYLL M139.003, from the imported `GaloisIntegerRing.Proofs` module) says
that the ambient value of this restricted ring automorphism applied to
`y : 𝒪[L]` is `σ y`. Applied to `y = x`, it closes the goal.

Besides the published definitions reached through the statement import, the
proof uses only M139.003 and Mathlib's `Units.ext` (through `ext`).

## Original source and modifications

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/Valuation.lean`,
lines 101–116 (docstring at line 101, theorem at lines 102–116). The file's
SHA-256 is
`478460e530e2a37ae4dc4eaad7db80d4dfa290f5bdd715a66d507ab2539579e0`.
The source proof is `intro hIntegerAction hFieldAction; ext; rfl`.

| Source declaration | Published proof declaration |
| --- | --- |
| `LocalClassFieldTheory.integerUnitsToFieldUnits_galoisGroup_equivariant` | `Langlands.NYLL.LocalClassFieldTheory.integerUnitsToFieldUnits_galoisGroup_equivariant` |

Modifications: the namespace prefix `Langlands.NYLL`; the focused statement
import plus the published `GaloisIntegerRing.Proofs` import; the result is
expressed as the published target proposition applied to all its parameters,
so the proof first unfolds that definition. The source's final `rfl` is
replaced by the `change` and the M139.003 application shown above. In the
source, the restriction `galoisGroupIntegerRingEquivOfIsIntegralClosure` is
built so that its ambient value is `σ` by definition. The published
restriction is built from Mathlib's `galRestrict'`, whose ambient value is
`σ` only propositionally, so `rfl` fails and the published `_apply` theorem
supplies the equality. The source `noncomputable section` and all other
source declarations are omitted.

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

This support lemma proves M140.007 only. It proves no host class-formation,
cup-product, transfer, Tate-cohomology or reciprocity target.

## Development validation

Lean service check `f2084ff0-94f8-45be-a5a9-b737a659ce4c` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled the proof without errors or
warnings; the inspected theorem has level parameter `u` and assumptions
`propext`, `Classical.choice` and `Quot.sound` only. Independent review,
exact-target validation and publication remain separate.
