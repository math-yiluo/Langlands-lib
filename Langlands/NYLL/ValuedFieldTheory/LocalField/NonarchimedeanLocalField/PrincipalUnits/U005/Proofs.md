# Antitonicity of the principal-unit filtration

This module proves `Langlands.NYLL.LocalFieldTheory.principalUnits_antitone`,
the proof phase of M131.005 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m131).
Its type is exactly the target
`Langlands.NYLL.LocalFieldTheory.principalUnits_antitoneStatement` applied to
the theorem's parameters.

## Theorem and target

```lean
theorem principalUnits_antitone (K : Type u) [Field K] [ValuativeRel K]
    {m n : Nat} (h : m ≤ n) :
    principalUnits_antitoneStatement K h
```

The parameters are the target's parameters in the target's order: a field
`K` in an arbitrary universe `u` with a `ValuativeRel K` instance, natural
numbers `m n` (implicit) and a proof `h : m ≤ n`. The target unfolds to
`principalUnits K n ≤ principalUnits K m`, inclusion of subgroups of
`𝒪[K]ˣ`: every unit `u` with `u - 1 ∈ 𝓂[K] ^ n` satisfies
`u - 1 ∈ 𝓂[K] ^ m`. All indices, including `m = 0`, are allowed. No
hypothesis is added.

## Implemented proof

The source tactic proof is kept unchanged:

```lean
  intro u hu
  exact Ideal.pow_le_pow_right h hu
```

`intro` unfolds the target and the subgroup order to
`∀ u, u ∈ principalUnits K n → u ∈ principalUnits K m` and introduces `u` and
`hu`. By the published definition of `principalUnits` (its carrier is
`{u | (u : 𝒪[K]) - 1 ∈ 𝓂[K] ^ n}`), `hu` is definitionally
`(u : 𝒪[K]) - 1 ∈ 𝓂[K] ^ n`. Mathlib's `Ideal.pow_le_pow_right`
(`Mathlib/RingTheory/Ideal/Operations.lean`) gives `I ^ n ≤ I ^ m` from
`m ≤ n`; applied to `hu` it yields `(u : 𝒪[K]) - 1 ∈ 𝓂[K] ^ m`, which is
definitionally `u ∈ principalUnits K m`. No auxiliary declaration is
introduced.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnits.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnits.lean#L78-L83):
the docstring at line 78 and the theorem at lines 79–83 (telescope and
conclusion at 79–81, tactics at 82–83); the task's unit range 79–85 ends
before the next declaration at 86. The retained original file has SHA-256
`1b36c019d270961f321ca891ae155fb4fd658d4e29ed97ba78e30fbee00a5047`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.principalUnits_antitone` | `Langlands.NYLL.LocalFieldTheory.principalUnits_antitone` |
| Its statement | `principalUnits_antitoneStatement K h` |

Modifications by Worker 134 on 14 November 2026: add the `Langlands.NYLL`
namespace prefix; give the theorem the target applied to its parameters as
its type; replace the source import by the single import of the statement
module; omit the source `noncomputable section` and all other source
declarations. The name, docstring, telescope and tactics are unchanged. The
partition records no patch10 change to this module.

## Imports

The sole import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.AntitoneQuotientStatements`,
which supplies the target and, through the published
`...PrincipalUnits.Definitions`, the subgroup `principalUnits` and Mathlib's
`Mathlib.RingTheory.Ideal.Operations` (for `Ideal.pow_le_pow_right`). That
module and everything it imports are left unchanged.

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

The source corollaries `principalUnits_succ_le` (M131.006) and
`principalUnits_le_one` (M131.007) are separate units and are not proved
here.

## Development check

The project Lean service compiled this module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings; the
theorem has level parameter `u` and uses only `propext`, `Classical.choice`
and `Quot.sound`. This is a development check, not exact-target validation
or independent acceptance.
