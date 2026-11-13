# Membership in the submodule `𝓂^(n+1)` of `𝓂^n`

This module proves
`Langlands.NYLL.LocalFieldTheory.mem_maximalIdealPowSuccSubmodule_iff`,
the proof phase of M132.068 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m132).
Its type is exactly the published target
`Langlands.NYLL.LocalFieldTheory.mem_maximalIdealPowSuccSubmodule_iffStatement`
applied to the theorem's parameters.

## Theorem and target

```lean
theorem mem_maximalIdealPowSuccSubmodule_iff
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u)) :
    mem_maximalIdealPowSuccSubmodule_iffStatement K n a
```

The parameters are the target's parameters in the target's order: the field
`K` in an arbitrary universe `u`, its `Field` and `ValuativeRel` instances,
an arbitrary natural depth `n` (including `0`) and an element `a` of the
ideal `𝓂[K] ^ n` of the valuation ring `𝒪[K]`, viewed as a subtype. The
target unfolds to

```lean
a ∈ maximalIdealPowSuccSubmodule K n ↔
  (a : 𝒪[K]) ∈ (𝓂[K] ^ (n + 1) : Ideal 𝒪[K])
```

No hypothesis is added. The imported abbreviation
`maximalIdealPowSuccSubmodule K n` is the `𝒪[K]`-submodule of `𝓂[K] ^ n`
defined as `Submodule.comap` of the ideal `𝓂[K] ^ (n + 1)` along the
subtype inclusion `𝓂[K] ^ n → 𝒪[K]`.

## Implemented proof

The proof term is `Iff.rfl`, as in the original. Membership in a
`Submodule.comap` along the subtype inclusion is by definition membership of
the image `(a : 𝒪[K])` in `𝓂[K] ^ (n + 1)`, so after unfolding the target
both sides of the iff are definitionally the same proposition. No
auxiliary declaration or lemma is used.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean`,
lines 909–916](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean#L909-L916):
the docstring at 909–910, the theorem telescope and conclusion at 911–915
and the proof term at 916 (the task's unit range 911–918 ends before the next
declaration). The complete retained original file has SHA-256
`6147c6613cd0176ace8787d7c65a3026d23bd5e23dc3282902d5ea66a0977c83`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.mem_maximalIdealPowSuccSubmodule_iff` | `Langlands.NYLL.LocalFieldTheory.mem_maximalIdealPowSuccSubmodule_iff` |
| Its statement | Published `mem_maximalIdealPowSuccSubmodule_iffStatement` |

Modifications by Worker 147 on 13 November 2026: add the `Langlands.NYLL`
namespace prefix; give the theorem the published target applied to its
parameters as its type; replace the source imports by the single import of
the statement module; omit the source `noncomputable section`,
`open Filter` and all other source declarations. The source docstring
repeats its single sentence twice; it is kept once, with a line break
adjusted. The theorem name, telescope and proof term `Iff.rfl` are
unchanged. The partition records no patch10 change to this module.

## Imports

The sole import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.QuotientAlgebraStatements`,
which supplies the target and, through
`...PrincipalUnitQuotients.MaximalIdealDefinitions`, the abbreviation
`maximalIdealPowSuccSubmodule`. That module and everything it imports are
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

This module proves only the stated membership criterion.

## Development check

The project Lean service compiled this module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings; the
theorem has level parameter `u` and uses only `propext`, `Classical.choice`
and `Quot.sound`. This is a development check, not exact-target validation
or independent acceptance.
