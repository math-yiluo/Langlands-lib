# Induction on classes of `𝓂^n/𝓂^(n+1)`

This module proves the protected theorem
`Langlands.NYLL.LocalFieldTheory.MaximalIdealPowSuccQuot.inductionOn`,
the proof phase of M132.062 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m132).
Its type is exactly the published protected target
`Langlands.NYLL.LocalFieldTheory.MaximalIdealPowSuccQuot.inductionOnStatement`
applied to the theorem's parameters.

## Theorem and target

```lean
protected theorem MaximalIdealPowSuccQuot.inductionOn
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : MaximalIdealPowSuccQuot K n → Prop}
    (q : MaximalIdealPowSuccQuot K n)
    (h : ∀ a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u),
      motive (maximalIdealPowSuccQuotMk K n a)) :
    MaximalIdealPowSuccQuot.inductionOnStatement n (motive := motive) q h
```

The parameters are the target's parameters in the target's order and with
its binder kinds: the implicit field `K` in an arbitrary universe `u`, its
`Field` and `ValuativeRel` instances, the explicit depth `n` (including
`0`), an implicit `Prop`-valued `motive` on the quotient, an explicit class
`q` and the explicit premise `h` that `motive` holds at the class of every
element `a` of the ideal `𝓂[K] ^ n`. The named argument
`(motive := motive)` only passes the implicit motive explicitly; the type is
the target applied to all of its parameters. The target unfolds to
`motive q`. No hypothesis is added; since the motive is `Prop`-valued the
theorem eliminates only into propositions.

The imported definitions are used unchanged:
`MaximalIdealPowSuccQuot K n` is the quotient `𝒪[K]`-module of the subtype
`𝓂[K] ^ n` by `maximalIdealPowSuccSubmodule K n`, the comap of
`𝓂[K] ^ (n + 1)` along the inclusion, and `maximalIdealPowSuccQuotMk K n`
is `Submodule.mkQ` for that submodule.

## Implemented proof

The proof follows the original unchanged:

```lean
change motive
  (show ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
    maximalIdealPowSuccSubmodule K n from q)
refine Quotient.inductionOn q ?_
intro a
exact h a
```

The `change` both unfolds the target to `motive q` and views `q` as an
element of the concrete submodule quotient, which is definitionally
`MaximalIdealPowSuccQuot K n`. The submodule quotient is a `Quotient` of a
setoid, so core Lean's `Quotient.inductionOn` reduces the goal to the
motive at the class of an arbitrary representative `a`. That class is
definitionally `maximalIdealPowSuccQuotMk K n a`, because `Submodule.mkQ`
sends `a` to its quotient class, and `h a` closes the goal. No auxiliary
declaration and no choice of representatives is used.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean`,
lines 817–830](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean#L817-L830):
the docstring at 817, the protected theorem telescope and conclusion at
818–824 and the proof at 825–830 (the task's unit range 818–832 ends before
the next declaration). The complete retained original file has SHA-256
`6147c6613cd0176ace8787d7c65a3026d23bd5e23dc3282902d5ea66a0977c83`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.MaximalIdealPowSuccQuot.inductionOn` (protected) | `Langlands.NYLL.LocalFieldTheory.MaximalIdealPowSuccQuot.inductionOn` (protected) |
| Its statement | Published protected `MaximalIdealPowSuccQuot.inductionOnStatement` |

Modifications by Worker 147 on 13 November 2026: add the `Langlands.NYLL`
namespace prefix; give the theorem the published target applied to its
parameters as its type; replace the source imports by the single import of
the statement module; omit the source `noncomputable section`,
`open Filter` and all other source declarations. The `protected` modifier,
theorem name, docstring, telescope and every proof step are unchanged; the
original first `change` also performs the unfolding of the target. The
partition records no patch10 change to this module.

## Imports

The sole import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.QuotientAlgebraStatements`,
which supplies the target and, through
`...PrincipalUnitQuotients.MaximalIdealDefinitions`, the quotient, its
defining submodule and class map. That module and everything it imports are
left unchanged.

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright
2026 Naganori Yamaguchi, author "Naganori Yamaguchi (assisted by OpenAI
Codex)", released under Apache-2.0. The Lean file carries the dated
modification record. The retained original belongs to the registered source
`external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), with
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`). No
errata note for either source ID exists in the project or Library `notes/`.
The unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) have SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. The
selected source file is not among the third-party paths listed in the
NOTICE. Worker 147 adapted this proof directly from the pinned original; no
other worker's draft is reused. The statement and definitions are Worker
211's, used unchanged.

This module proves only unary induction. The binary induction M132.063 is a
separate unit with its own proof module.

## Development check

The project Lean service compiled this module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings; the
theorem has level parameter `u` and uses only `propext`, `Classical.choice`
and `Quot.sound`. This is a development check, not exact-target validation
or independent acceptance.
