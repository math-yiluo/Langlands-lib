# A unit identity for valuation-ring units

This module proves `Langlands.NYLL.LocalFieldTheory.unit_mul_sub_one_eq`,
the proof phase of M131.020 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m131).
Its type is exactly the target
`Langlands.NYLL.LocalFieldTheory.unit_mul_sub_one_eqStatement` applied to the
theorem's parameters.

## Theorem and target

```lean
theorem unit_mul_sub_one_eq (K : Type u) [Field K] [ValuativeRel K] (a b : 𝒪[K]ˣ) :
    unit_mul_sub_one_eqStatement K a b
```

The parameters are the target's parameters in the target's order: a field
`K` in an arbitrary universe `u` with a `ValuativeRel K` instance, and two
units `a b` of its valuation ring `𝒪[K]`. The target unfolds to the identity

`((a * b : 𝒪[K]ˣ) : 𝒪[K]) - 1 = ((a : 𝒪[K]) - 1) * ((b : 𝒪[K]) - 1) + ((a : 𝒪[K]) - 1) + ((b : 𝒪[K]) - 1)`

in the commutative ring `𝒪[K]`, where `(a * b : 𝒪[K]ˣ)` is the product in the
unit group and the coercions are `Units.val`. No hypothesis is added.

## Implemented proof

```lean
  unfold unit_mul_sub_one_eqStatement
  simp only [Units.val_mul]
  ring
```

`unfold` replaces the target by its defining equation. Mathlib's
`Units.val_mul` (`↑(a * b) = ↑a * ↑b`) rewrites the coerced unit product to the
product of the coerced units, and `ring` closes the resulting commutative-ring
identity `xy - 1 = (x - 1)(y - 1) + (x - 1) + (y - 1)`. No auxiliary
declaration is introduced. The two source tactics are kept unchanged; the
`unfold` line is added because the target is a named `Prop`-valued
definition that `simp only [Units.val_mul]` does not unfold.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnits.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnits.lean#L199-L205):
the docstring at line 199 and the lemma at lines 200–205 (telescope and
conclusion at 200–203, tactics at 204–205); the task's unit range 200–207
ends before the next declaration at 208. The retained original file has
SHA-256 `1b36c019d270961f321ca891ae155fb4fd658d4e29ed97ba78e30fbee00a5047`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.unit_mul_sub_one_eq` (a `lemma`) | `Langlands.NYLL.LocalFieldTheory.unit_mul_sub_one_eq` (a `theorem`) |
| Its statement | `unit_mul_sub_one_eqStatement K a b` |

Modifications by Worker 134 on 14 November 2026: add the `Langlands.NYLL`
namespace prefix; declare the source `lemma` with the keyword `theorem`
(the same kind of declaration); give it the target applied to its parameters
as its type; add the `unfold unit_mul_sub_one_eqStatement` line before the
unchanged source tactics; replace the source import by the single import of
the statement module; omit the source `noncomputable section` and all other
source declarations. The name, docstring and telescope are unchanged. The
partition records no patch10 change to this module.

## Imports

The sole import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.AntitoneQuotientStatements`,
which supplies the target; `𝒪[K]`, `Units.val_mul` and `ring` come through
its imports (the published `...PrincipalUnits.Definitions`, which imports
`Mathlib.Topology.Algebra.Valued.ValuativeRel` and `Mathlib.Tactic.Ring`).
That module and everything it imports are left unchanged.

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright
2026 Naganori Yamaguchi, author "Naganori Yamaguchi (assisted by OpenAI
Codex)", released under Apache-2.0. The Lean file carries the dated
modification record. The retained original belongs to the registered source
`external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), with
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`). The
unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) have SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. Worker
134 adapted this proof directly from the pinned original. The statement is
Worker 346's, used unchanged.

This module proves only the identity; the antitonicity M131.005 and the
quotient induction M131.019 are separate units.

## Development check

The project Lean service compiled this module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings; the
theorem has level parameter `u` and uses only `propext`, `Classical.choice`
and `Quot.sound`. This is a development check, not exact-target validation
or independent acceptance.
