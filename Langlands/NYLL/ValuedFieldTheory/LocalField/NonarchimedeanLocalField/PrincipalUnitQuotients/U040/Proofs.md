# Surjectivity of the successive principal-unit quotient map

This module proves
`Langlands.NYLL.LocalFieldTheory.principalUnitsSuccQuotMk_surjective`,
the proof phase of M132.040 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m132).
Its type is exactly the published target
`Langlands.NYLL.LocalFieldTheory.principalUnitsSuccQuotMk_surjectiveStatement`
applied to the theorem's parameters.

## Theorem and target

```lean
theorem principalUnitsSuccQuotMk_surjective
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    principalUnitsSuccQuotMk_surjectiveStatement K n
```

The parameters are the target's parameters in the target's order: the field
`K` in an arbitrary universe `u`, its `Field` and `ValuativeRel` instances
and an arbitrary natural depth `n` (including `0`). The target unfolds to
`Function.Surjective (principalUnitsSuccQuotMk K n)`: every class of
`U^n/U^(n+1)` is the class of some `u : principalUnits K n`. No hypothesis
is added.

The imported definitions are used unchanged: `PrincipalUnitsSuccQuot K n`
is the quotient group of `principalUnits K n` by the embedded subgroup
`(principalUnits K (n + 1)).subgroupOf (principalUnits K n)`, and
`principalUnitsSuccQuotMk K n` is `QuotientGroup.mk'` for that subgroup.

## Implemented proof

The proof term is the original one,

```lean
QuotientGroup.mk'_surjective ((principalUnits K (n + 1)).subgroupOf (principalUnits K n))
```

Mathlib's `QuotientGroup.mk'_surjective`
(`Mathlib/GroupTheory/QuotientGroup/Defs.lean`) states that
`QuotientGroup.mk' N` is surjective for a normal subgroup `N`; here `N` is
normal because `principalUnits K n` is commutative. The term is accepted at
the target type because `principalUnitsSuccQuotMk K n` and the named
quotient unfold definitionally to `QuotientGroup.mk' N` and its concrete
codomain. No auxiliary declaration is introduced.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean`,
lines 593–597](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean#L593-L597):
the docstring at 593, the theorem telescope and conclusion at 594–596 and
the proof term at 597 (the task's unit range 594–599 ends before the next
declaration). The complete retained original file has SHA-256
`6147c6613cd0176ace8787d7c65a3026d23bd5e23dc3282902d5ea66a0977c83`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.principalUnitsSuccQuotMk_surjective` | `Langlands.NYLL.LocalFieldTheory.principalUnitsSuccQuotMk_surjective` |
| Its statement | Published `principalUnitsSuccQuotMk_surjectiveStatement` |

Modifications by Worker 147 on 13 November 2026: add the `Langlands.NYLL`
namespace prefix; give the theorem the published target applied to its
parameters as its type; replace the source imports by the single import of
the statement module; omit the source `noncomputable section`,
`open Filter` and all other source declarations. The theorem name,
docstring, telescope and proof term are unchanged. The partition records no
patch10 change to this module.

## Imports

The sole import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.QuotientAlgebraStatements`,
which supplies the target and, through
`...PrincipalUnitQuotients.SuccessorDefinitions`, the quotient and quotient
map, with Mathlib's `Mathlib.GroupTheory.QuotientGroup.Basic`. That module
and everything it imports are left unchanged.

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

This module proves only surjectivity; the kernel and range descriptions
M132.041–M132.045 are separate units.

## Development check

The project Lean service compiled this module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings; the
theorem has level parameter `u` and uses only `propext`, `Classical.choice`
and `Quot.sound`. This is a development check, not exact-target validation
or independent acceptance.
