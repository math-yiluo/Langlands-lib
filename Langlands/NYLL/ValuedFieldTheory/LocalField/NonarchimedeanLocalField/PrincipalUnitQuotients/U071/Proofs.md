# Invertibility of `1 + a` for `a` in a positive maximal-ideal power

This module proves
`Langlands.NYLL.LocalFieldTheory.isUnit_one_add_of_mem_maximalIdeal_pow`,
the proof phase of M132.071 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m132).
Its type is exactly the published target
`Langlands.NYLL.LocalFieldTheory.isUnit_one_add_of_mem_maximalIdeal_powStatement`
applied to the theorem's parameters.

## Theorem and target

```lean
theorem isUnit_one_add_of_mem_maximalIdeal_pow
    (K : Type u) [Field K] [ValuativeRel K] {n : Nat} (hn : 1 ≤ n)
    (a : 𝒪[K]) (ha : a ∈ (𝓂[K] ^ n : Ideal 𝒪[K])) :
    isUnit_one_add_of_mem_maximalIdeal_powStatement K hn a ha
```

The parameters are the target's parameters in the target's order and with
its binder kinds: the field `K` in an arbitrary universe `u`, its `Field`
and `ValuativeRel` instances, the implicit depth `n`, the explicit premise
`hn : 1 ≤ n`, an element `a` of the valuation ring and the explicit premise
`ha` that `a` lies in the `n`-th power of the maximal ideal. Here, under
`open scoped ValuativeRel`, `𝒪[K]` is
`Valuation.integer (ValuativeRel.valuation K)` and `𝓂[K]` is
`IsLocalRing.maximalIdeal 𝒪[K]`. The target unfolds to `IsUnit (1 + a)` in
the valuation ring `𝒪[K]`. No topology, completeness, discreteness,
residue-finiteness or nontrivial-valuation hypothesis is added.

## Implemented proof

The proof first states the unfolded goal `IsUnit (1 + a)` with `show`; this
is a definitional unfolding of the target. It then follows the original
proof unchanged:

1. `ha1 : a ∈ 𝓂[K]`. From `hn : 1 ≤ n`, Mathlib's `Ideal.pow_le_pow_right`
   (`Mathlib/RingTheory/Ideal/Operations.lean`) gives
   `𝓂[K] ^ n ≤ 𝓂[K] ^ 1`; applying it to `ha` and letting `simpa` rewrite
   `𝓂[K] ^ 1` to `𝓂[K]` gives membership in `𝓂[K]`.
2. `hnon : -a ∈ nonunits 𝒪[K]`. Rewriting backwards with
   `IsLocalRing.mem_maximalIdeal`
   (`Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean`) turns the goal
   into `-a ∈ 𝓂[K]`, which is `Submodule.neg_mem` applied to `ha1`.
3. `hunit : IsUnit (1 - (-a))` is
   `IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-a) hnon`
   (`Mathlib/RingTheory/LocalRing/Basic.lean`); the valuation ring is a local
   ring.
4. `simpa [sub_neg_eq_add] using hunit` rewrites `1 - (-a)` to `1 + a` and
   closes the goal.

The premise `hn` is used in step 1; without it the claim fails at `n = 0`
(for example `a = -1`). The proof introduces no auxiliary declaration and
uses only the definitions imported with the target and the Mathlib lemmas
named above.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean`,
lines 945–958](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean#L945-L958):
the docstring at line 945, the theorem telescope and conclusion at 946–948
and the proof at 948–958 (the task's unit range 946–960 ends before the next
declaration). The complete retained original file has SHA-256
`6147c6613cd0176ace8787d7c65a3026d23bd5e23dc3282902d5ea66a0977c83`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.isUnit_one_add_of_mem_maximalIdeal_pow` | `Langlands.NYLL.LocalFieldTheory.isUnit_one_add_of_mem_maximalIdeal_pow` |
| Its statement | Published `isUnit_one_add_of_mem_maximalIdeal_powStatement` |

Modifications by Worker 147 on 13 November 2026: add the `Langlands.NYLL`
namespace prefix; give the theorem the published target applied to its
parameters as its type and add the leading `show IsUnit (1 + a)`; replace
the source imports by the single import of the statement module; omit the
source `noncomputable section`, `open Filter` and all other source
declarations. The theorem name, docstring, telescope and the remaining proof
steps are unchanged. The partition records no patch10 change to this module,
and the original proof needed no change for the approved environment.

## Imports

The sole import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.QuotientAlgebraStatements`,
which supplies the target and, through its imports, the published
`principalUnits` definitions and Mathlib's valuative-relation, ideal and
local-ring API used above. That module and everything it imports are left
unchanged.

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

This module proves only the stated invertibility. The correction-unit
construction M132.072 and the later quotient comparisons are separate units.

## Development check

The project Lean service compiled this module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings; the
theorem has level parameter `u` and uses only `propext`, `Classical.choice`
and `Quot.sound`. This is a development check, not exact-target validation
or independent acceptance.
