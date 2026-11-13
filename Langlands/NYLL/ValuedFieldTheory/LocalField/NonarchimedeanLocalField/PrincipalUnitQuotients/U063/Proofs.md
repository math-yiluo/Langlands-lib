# Binary induction on classes of `𝓂^n/𝓂^(n+1)`

This module proves the protected theorem
`Langlands.NYLL.LocalFieldTheory.MaximalIdealPowSuccQuot.inductionOn2`,
the proof phase of M132.063 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m132).
Its type is exactly the published protected target
`Langlands.NYLL.LocalFieldTheory.MaximalIdealPowSuccQuot.inductionOn2Statement`
applied to the theorem's parameters. The module also declares the
source-named theorem `MaximalIdealPowSuccQuot.inductionOn₂`, whose type is
the published `MaximalIdealPowSuccQuot.inductionOn₂Statement` and whose
proof is the submitted theorem. It is not the submitted target.

## Why two names

The source theorem is called `inductionOn₂`, and the original M132.063
target `MaximalIdealPowSuccQuot.inductionOn₂Statement` (in
`PrincipalUnitQuotients/QuotientAlgebraStatements.lean`) keeps that name.
The `lean.proof@1` submission schema accepts only ASCII qualified names for
the proof and statement declarations, so a proof of that target cannot be
submitted under the source name. The published ASCII wrapper
`inductionOn2Statement` (module
`PrincipalUnitQuotients.InductionOn2Statement`, Worker 5264) applies
`inductionOn₂Statement` to the same arguments. Task 5994 revision 2
therefore requires the theorem `inductionOn2` with the wrapper as its type,
and permits the source-named theorem as an optional consequence.

## Theorems and targets

```lean
protected theorem MaximalIdealPowSuccQuot.inductionOn2
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : MaximalIdealPowSuccQuot K n →
      MaximalIdealPowSuccQuot K n → Prop}
    (q r : MaximalIdealPowSuccQuot K n)
    (h : ∀ a b : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u),
      motive (maximalIdealPowSuccQuotMk K n a)
        (maximalIdealPowSuccQuotMk K n b)) :
    MaximalIdealPowSuccQuot.inductionOn2Statement n (motive := motive) q r h

protected theorem MaximalIdealPowSuccQuot.inductionOn₂
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : MaximalIdealPowSuccQuot K n →
      MaximalIdealPowSuccQuot K n → Prop}
    (q r : MaximalIdealPowSuccQuot K n)
    (h : ∀ a b : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u),
      motive (maximalIdealPowSuccQuotMk K n a)
        (maximalIdealPowSuccQuotMk K n b)) :
    MaximalIdealPowSuccQuot.inductionOn₂Statement n (motive := motive) q r h
```

Both theorems take the target's parameters in the target's order and with
its binder kinds. These are the implicit field `K` in an arbitrary universe
`u` with its `Field` and `ValuativeRel` instances, and the explicit depth
`n`, which may be `0`. Then come an implicit two-variable `Prop`-valued
`motive` on the quotient, two explicit classes `q r`, and the explicit
premise `h`. The premise says that `motive` holds at the classes of every
pair `a b` of elements of the ideal `𝓂[K] ^ n`. The named argument
`(motive := motive)` only passes the implicit motive explicitly. The wrapper
`inductionOn2Statement` is by definition `inductionOn₂Statement` applied to
the same arguments, and `inductionOn₂Statement` is by definition
`motive q r`. No hypothesis is added, and the motive is an arbitrary
two-variable predicate.

The imported definitions are used unchanged.
`MaximalIdealPowSuccQuot K n` is the quotient `𝒪[K]`-module of the subtype
`𝓂[K] ^ n` by `maximalIdealPowSuccSubmodule K n`.
`maximalIdealPowSuccQuotMk K n` is `Submodule.mkQ` for that submodule.

## Implemented proof

The proof of `inductionOn2` is

```lean
show motive q r
refine MaximalIdealPowSuccQuot.inductionOn n
  (motive := fun q' => motive q' r) q ?_
intro a
refine MaximalIdealPowSuccQuot.inductionOn n
  (motive := fun r' => motive (maximalIdealPowSuccQuotMk K n a) r') r ?_
intro b
exact h a b
```

The `show` unfolds the wrapper target, through `inductionOn₂Statement`, to
`motive q r`. The proof then uses the published M132.062 theorem
`MaximalIdealPowSuccQuot.inductionOn` (module `PrincipalUnitQuotients.U062.Proofs`).
Its type is `inductionOnStatement n (motive := motive) q h`, which is by
definition `motive q`. The first application has motive
`fun q' => motive q' r` and reduces the goal for `q` to the classes
`maximalIdealPowSuccQuotMk K n a` of representatives `a`. The second
application has motive `fun r' => motive (maximalIdealPowSuccQuotMk K n a) r'`
and does the same for `r` with representatives `b`. Lean's definitional
unfolding identifies each `inductionOnStatement` instance with the current
goal. The remaining goal is `motive` at the classes of `a` and `b`, which
`h a b` closes.

The source-named theorem is proved by the term
`MaximalIdealPowSuccQuot.inductionOn2 n (motive := motive) q r h`. Its type
`inductionOn2Statement ...` is by definition the required
`inductionOn₂Statement ...`.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean`,
lines 832–848](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean#L832-L848).
Line 832 is the docstring, lines 833–841 the protected theorem telescope and
conclusion, and lines 842–848 the proof. The task's unit range 833–851 ends
before the next declaration. The complete retained original file has
SHA-256 `6147c6613cd0176ace8787d7c65a3026d23bd5e23dc3282902d5ea66a0977c83`.
The source proof (lines 842–848) is the proof of `inductionOn2` above
without its first line `show motive q r`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.MaximalIdealPowSuccQuot.inductionOn₂` (protected) | `Langlands.NYLL.LocalFieldTheory.MaximalIdealPowSuccQuot.inductionOn2` (protected, submitted) and `Langlands.NYLL.LocalFieldTheory.MaximalIdealPowSuccQuot.inductionOn₂` (protected, derived) |
| Its statement | Published protected `MaximalIdealPowSuccQuot.inductionOn2Statement` (ASCII wrapper) and `MaximalIdealPowSuccQuot.inductionOn₂Statement` |
| `LocalFieldTheory.MaximalIdealPowSuccQuot.inductionOn` (M132.062), used by the source proof | Published `Langlands.NYLL.LocalFieldTheory.MaximalIdealPowSuccQuot.inductionOn`, imported |

Modifications by Worker 147 on 13 November 2026:

- add the `Langlands.NYLL` namespace prefix;
- name the submitted theorem `inductionOn2` with the ASCII wrapper target as
  its type, and add the leading `show motive q r` that unfolds it;
- keep the source name `inductionOn₂` as a second theorem, typed by the
  published `inductionOn₂Statement` and proved from `inductionOn2`;
- replace the source imports by the imports listed below; omit the source
  `noncomputable section`, `open Filter` and all other source declarations.

The `protected` modifier, docstring, telescope and the seven source proof
lines are unchanged. The partition records no patch10 change to this module.

## Imports

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.InductionOn2Statement`
  supplies the wrapper target. Through
  `...PrincipalUnitQuotients.QuotientAlgebraStatements` and
  `...PrincipalUnitQuotients.MaximalIdealDefinitions` it also supplies
  `inductionOn₂Statement`, the quotient, its defining submodule and the
  class map.
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.U062.Proofs`
  supplies the published M132.062 theorem `MaximalIdealPowSuccQuot.inductionOn`.

These modules and everything they import are unchanged.

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
other worker's draft is reused. The original statement and definitions are
Worker 211's, and the ASCII wrapper is Worker 5264's; all are used unchanged.

This module proves only binary induction.

## Development check

The project Lean service compiled this module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings. The
theorem `inductionOn2` has level parameter `u` and uses only `propext`,
`Classical.choice` and `Quot.sound`. This is a development check, not
exact-target validation or independent acceptance.
