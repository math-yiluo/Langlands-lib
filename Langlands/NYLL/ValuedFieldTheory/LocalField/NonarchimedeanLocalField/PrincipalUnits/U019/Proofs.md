# Induction on the quotient of valuation-ring units by principal units

This module proves
`Langlands.NYLL.LocalFieldTheory.IntegerUnitsPrincipalQuot.inductionOn`, the
proof phase of M131.019 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m131).
Its type is exactly the target
`Langlands.NYLL.LocalFieldTheory.IntegerUnitsPrincipalQuot.inductionOnStatement`
applied to the theorem's parameters.

## Theorem and target

```lean
protected theorem IntegerUnitsPrincipalQuot.inductionOn
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : IntegerUnitsPrincipalQuot K n → Prop}
    (q : IntegerUnitsPrincipalQuot K n)
    (h : ∀ u : 𝒪[K]ˣ, motive (integerUnitsPrincipalQuotMk K n u)) :
    IntegerUnitsPrincipalQuot.inductionOnStatement n (motive := motive) q h
```

The parameters are the target's parameters in the target's order and with
the target's binder kinds: an implicit field `K` in an arbitrary universe `u`
with a `ValuativeRel K` instance, a natural index `n` (including `0`), an
implicit predicate `motive` on the quotient
`IntegerUnitsPrincipalQuot K n = 𝒪[K]ˣ ⧸ principalUnits K n`, a class `q`, and
a proof `h` that `motive` holds at the class
`integerUnitsPrincipalQuotMk K n u` of every unit `u`. The target unfolds to
`motive q`. The named argument `(motive := motive)` only passes the implicit
predicate explicitly; it is the one Lean would infer from `h`. Like the source
theorem and the target, the theorem is `protected`. No hypothesis is added.

## Implemented proof

The source tactic proof is kept unchanged:

```lean
  change motive (show 𝒪[K]ˣ ⧸ principalUnits K n from q)
  refine QuotientGroup.induction_on q ?_
  intro u
  exact h u
```

`change` replaces the target by `motive q` with `q` viewed in the concrete
quotient `𝒪[K]ˣ ⧸ principalUnits K n`, which is the published definition of
`IntegerUnitsPrincipalQuot K n`. Mathlib's `QuotientGroup.induction_on`
(`Mathlib/GroupTheory/Coset/Defs.lean`) reduces `motive q` to
`motive (QuotientGroup.mk u)` for every `u : 𝒪[K]ˣ`. The published
`integerUnitsPrincipalQuotMk K n` is `QuotientGroup.mk' (principalUnits K n)`,
whose value at `u` is definitionally `QuotientGroup.mk u`, so `h u` closes each
case. No auxiliary declaration is introduced.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnits.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnits.lean#L186-L197):
the docstring at lines 186–187 and the theorem at lines 188–197 (telescope
and conclusion at 188–193, tactics at 194–197); the task's unit range
188–199 ends before the next declaration at 200. The retained original file
has SHA-256
`1b36c019d270961f321ca891ae155fb4fd658d4e29ed97ba78e30fbee00a5047`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.IntegerUnitsPrincipalQuot.inductionOn` | `Langlands.NYLL.LocalFieldTheory.IntegerUnitsPrincipalQuot.inductionOn` |
| Its statement | `IntegerUnitsPrincipalQuot.inductionOnStatement n (motive := motive) q h` |

Modifications by Worker 134 on 14 November 2026: add the `Langlands.NYLL`
namespace prefix; give the theorem the target applied to its parameters as
its type; replace the source import by the single import of the statement
module; omit the source `noncomputable section` and all other source
declarations. The name, `protected` modifier, docstring, telescope and
tactics are unchanged. The partition records no patch10 change to this
module.

## Imports

The sole import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.AntitoneQuotientStatements`,
which supplies the target and, through
`...PrincipalUnits.QuotientDefinitions`, the quotient
`IntegerUnitsPrincipalQuot`, its group structure, the class map
`integerUnitsPrincipalQuotMk` and Mathlib's
`Mathlib.GroupTheory.QuotientGroup.Basic`. That module and everything it
imports are left unchanged.

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
134 adapted this proof directly from the pinned original. The statement and
the quotient definitions are Worker 346's, used unchanged.

This module proves only the induction principle; the other quotient
interface results of the source (M131.010, M131.012–M131.018) are separate
units.

## Development check

The project Lean service compiled this module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings; the
theorem has level parameter `u` and uses only `propext`, `Classical.choice`
and `Quot.sound`. This is a development check, not exact-target validation
or independent acceptance.
