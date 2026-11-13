# Products of two elements of a positive maximal-ideal power

This module proves
`Langlands.NYLL.LocalFieldTheory.maximalIdealPow_mul_mem_succ`,
the proof phase of M132.086 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m132).
Its type is exactly the published target
`Langlands.NYLL.LocalFieldTheory.maximalIdealPow_mul_mem_succStatement`
applied to the theorem's parameters.

## Theorem and target

```lean
theorem maximalIdealPow_mul_mem_succ
    (K : Type u) [Field K] [ValuativeRel K] {n : Nat} (hn : 1 ≤ n)
    (a b : (𝓂[K] ^ n : Ideal 𝒪[K])) :
    maximalIdealPow_mul_mem_succStatement K hn a b
```

The parameters are the target's parameters in the target's order and with
its binder kinds: the field `K` in an arbitrary universe `u`, its `Field`
and `ValuativeRel` instances, the implicit depth `n`, the explicit premise
`hn : 1 ≤ n` and two elements `a b` of the ideal `𝓂[K] ^ n` of the
valuation ring `𝒪[K]`, viewed as a subtype. Under `open scoped ValuativeRel`,
`𝒪[K]` is `Valuation.integer (ValuativeRel.valuation K)` and `𝓂[K]` its
maximal ideal. The target unfolds to

```lean
((a : 𝒪[K]) * (b : 𝒪[K])) ∈ (𝓂[K] ^ (n + 1) : Ideal 𝒪[K])
```

No hypothesis is added.

## Implemented proof

The proof first states the unfolded membership with `show`, a definitional
unfolding of the target, then follows the original proof unchanged:

1. `hmul : (a : 𝒪[K]) * (b : 𝒪[K]) ∈ 𝓂[K] ^ (n + n)`. Mathlib's
   `Ideal.mul_mem_mul` (`Mathlib/RingTheory/Ideal/Operations.lean`) applied
   to the membership proofs `a.2` and `b.2` gives membership in
   `𝓂[K] ^ n * 𝓂[K] ^ n`, and `simpa [pow_add]` identifies this ideal with
   `𝓂[K] ^ (n + n)`.
2. `hle : 𝓂[K] ^ (n + n) ≤ 𝓂[K] ^ (n + 1)`. Since `1 ≤ n`,
   `Nat.add_le_add_left hn n` gives `n + 1 ≤ n + n`, and
   `Ideal.pow_le_pow_right` (same file) turns this into the reverse
   inclusion of ideal powers.
3. `exact hle hmul`.

The premise `hn` is used in step 2; without it the claim fails at `n = 0`
(for `a = b = 1`). No auxiliary declaration is introduced.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean`,
lines 1160–1170](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean#L1160-L1170):
the docstring at 1160, the theorem telescope and conclusion at 1161–1164
and the proof at 1164–1170 (the task's unit range 1161–1173 ends before the
next declaration). The complete retained original file has SHA-256
`6147c6613cd0176ace8787d7c65a3026d23bd5e23dc3282902d5ea66a0977c83`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.maximalIdealPow_mul_mem_succ` | `Langlands.NYLL.LocalFieldTheory.maximalIdealPow_mul_mem_succ` |
| Its statement | Published `maximalIdealPow_mul_mem_succStatement` |

Modifications by Worker 147 on 13 November 2026: add the `Langlands.NYLL`
namespace prefix; give the theorem the published target applied to its
parameters as its type and add the leading `show`; replace the source
imports by the single import of the statement module; omit the source
`noncomputable section`, `open Filter` and all other source declarations.
The theorem name, docstring, telescope and the remaining proof steps are
unchanged. The partition records no patch10 change to this module, and the
original proof needed no change for the approved environment.

## Imports

The sole import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.QuotientAlgebraStatements`,
which supplies the target and, through its imports, Mathlib's
valuative-relation and ideal API (`Mathlib.RingTheory.Ideal.Operations`)
used above. That module and everything it imports are left unchanged.

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
other worker's draft is reused. The statement is Worker 211's, used
unchanged.

This module proves only the stated ideal-depth property; the product
formula M132.087 and the quotient comparisons are separate units.

## Development check

The project Lean service compiled this module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings; the
theorem has level parameter `u` and uses only `propext`, `Classical.choice`
and `Quot.sound`. This is a development check, not exact-target validation
or independent acceptance.
