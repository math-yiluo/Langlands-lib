# NYLL M140.004: the Galois action on integer units

Worker 120, 14 November 2026.

## Statement and scope

This pair proves the published proposition
`Langlands.NYLL.LocalClassFieldTheory.galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smulStatement`
under the required theorem name
`Langlands.NYLL.LocalClassFieldTheory.galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul`.
The theorem's type is the target applied to all its parameters:
fields `K` and `L` in one universe `u` with valuative relations, a
`K`-algebra structure on `L`, the valuation-extension instance, the
integral-closure instance `IsIntegralClosure 𝒪[L] 𝒪[K] L`, a Galois
automorphism `σ : Gal(L/K)` and an integer unit `x : 𝒪[L]ˣ`.
Its sole import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.IntegerStatements`.
The published statement and its imported definitions remain unchanged.

The statement says that, under the local action
`galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L`,

```lean
σ • x = Units.mapEquiv
  (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).toMulEquiv x
```

that is, `σ` acts on an integer unit by applying the ring automorphism of
`𝒪[L]` obtained by restricting `σ`.

## Implemented proof

```lean
  unfold galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smulStatement
  intro hIntegerAction
  apply Units.ext
  rfl
```

The target definition is unfolded so that its local action binder can be
introduced. `Units.ext` reduces the equality of units to the equality of
their values in `𝒪[L]`. The action is Mathlib's
`Units.mulDistribMulActionRight` built from the published semiring action
`galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure K L`, which is
`MulSemiringAction.compHom` along the hom
`galoisGroupIntegerRingEquivHomOfIsIntegralClosure K L`, whose underlying
function is `galoisGroupIntegerRingEquivOfIsIntegralClosure K L`. Hence the
value of `σ • x` is that ring automorphism applied to the value of `x`, as is
the value of the right-hand side; `rfl` closes the goal.

The proof uses only these published definitions, reached through the
statement import, and Mathlib's `Units.ext`. It invokes no other NYLL
theorem.

## Original source and modifications

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/Valuation.lean`,
lines 62–76 (docstring at line 62, `@[simp]` at line 63, theorem at
lines 64–76). The file's SHA-256 is
`478460e530e2a37ae4dc4eaad7db80d4dfa290f5bdd715a66d507ab2539579e0`.
The source proof is `intro hIntegerAction; apply Units.ext; rfl`.

| Source declaration | Published proof declaration |
| --- | --- |
| `LocalClassFieldTheory.galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul` | `Langlands.NYLL.LocalClassFieldTheory.galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure_smul` |

Modifications: the namespace prefix `Langlands.NYLL`; the focused statement
import; the result is expressed as the published target proposition applied
to all its parameters, so the proof first unfolds that definition; the
theorem-only `@[simp]` attribute, the source `noncomputable section` and all
other source declarations are omitted. The published restriction
`galoisGroupIntegerRingEquivOfIsIntegralClosure` is defined with Mathlib's
`galRestrict'` rather than by the source construction; this proof does not
depend on that difference, since both sides use the same published map.

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

This support lemma proves M140.004 only. It proves no host class-formation,
cup-product, transfer, Tate-cohomology or reciprocity target.

## Development validation

Lean service check `3dd51b67-184d-4065-b23a-bc22cc70edc5` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled the proof without errors or
warnings; the inspected theorem has level parameter `u` and assumptions
`propext`, `Classical.choice` and `Quot.sound` only. Independent review,
exact-target validation and publication remain separate.
