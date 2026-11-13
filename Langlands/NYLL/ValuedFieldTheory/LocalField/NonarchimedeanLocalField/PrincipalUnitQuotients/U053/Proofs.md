# Membership in the embedded successor subgroup

This module proves
`Langlands.NYLL.LocalFieldTheory.mem_principalUnits_succ_subgroupOf_iff`,
the proof phase of M132.053 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m132).
Its type is exactly the published target
`Langlands.NYLL.LocalFieldTheory.mem_principalUnits_succ_subgroupOf_iffStatement`
applied to the theorem's parameters.

## Theorem and target

```lean
theorem mem_principalUnits_succ_subgroupOf_iff
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (u : principalUnits K n) :
    mem_principalUnits_succ_subgroupOf_iffStatement K n u
```

The parameters are the target's parameters in the target's order: the field
`K` in an arbitrary universe `u`, its `Field` and `ValuativeRel` instances,
an arbitrary natural depth `n` (including `0`) and an element `u` of the
principal-unit subgroup `principalUnits K n` of `𝒪[K]ˣ`. Under
`open scoped ValuativeRel`, `𝒪[K]` is the valuation ring
`Valuation.integer (ValuativeRel.valuation K)` and `𝓂[K]` its maximal ideal.
The target unfolds to

```lean
u ∈ (principalUnits K (n + 1)).subgroupOf (principalUnits K n) ↔
  (((u : 𝒪[K]ˣ) : 𝒪[K]) - 1) ∈ (𝓂[K] ^ (n + 1) : Ideal 𝒪[K])
```

so `u` lies in the copy of `U^(n+1)` inside `U^n` exactly when the
underlying valuation-ring element of `u` is congruent to `1` modulo
`𝓂[K] ^ (n + 1)`. No hypothesis is added.

## Implemented proof

The proof first states the unfolded iff with `show`, a definitional
unfolding of the target, and then performs the original rewrite:

```lean
rw [Subgroup.mem_subgroupOf, mem_principalUnits_iff K (u : 𝒪[K]ˣ) (n + 1)]
```

Mathlib's `Subgroup.mem_subgroupOf`
(`Mathlib/Algebra/Group/Subgroup/Map.lean`) turns membership in the
`subgroupOf` into membership of the coerced unit `(u : 𝒪[K]ˣ)` in
`principalUnits K (n + 1)`. The published M131.002 theorem
`Langlands.NYLL.LocalFieldTheory.mem_principalUnits_iff` then rewrites that
membership into `((u : 𝒪[K]ˣ) : 𝒪[K]) - 1 ∈ 𝓂[K] ^ (n + 1)`, and `rw`
closes the resulting reflexive iff. The published M131.002 theorem has the
closed proposition `MemPrincipalUnitsIffStatement.{u}` as its type, whose
body is
`∀ (K : Type u) [Field K] [ValuativeRel K] (a : 𝒪[K]ˣ) (n : Nat),
a ∈ principalUnits K n ↔ ((a : 𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal 𝒪[K])`;
the proof therefore supplies its explicit arguments `K`, `(u : 𝒪[K]ˣ)` and
`n + 1` before rewriting, where the source wrote the bare name. No
auxiliary declaration is introduced.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean`,
lines 737–745](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean#L737-L745):
the docstring at 737–738, the theorem telescope and conclusion at 739–744
and the proof at 744–745 (the task's unit range 739–747 ends before the next
declaration). The complete retained original file has SHA-256
`6147c6613cd0176ace8787d7c65a3026d23bd5e23dc3282902d5ea66a0977c83`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.mem_principalUnits_succ_subgroupOf_iff` | `Langlands.NYLL.LocalFieldTheory.mem_principalUnits_succ_subgroupOf_iff` |
| Its statement | Published `mem_principalUnits_succ_subgroupOf_iffStatement` |
| `LocalFieldTheory.mem_principalUnits_iff` (`PrincipalUnits.lean`, M131.002) | Published `Langlands.NYLL.LocalFieldTheory.mem_principalUnits_iff` |

Modifications by Worker 147 on 13 November 2026: add the `Langlands.NYLL`
namespace prefix; give the theorem the published target applied to its
parameters as its type and add the leading `show`; apply the published
M131.002 theorem to its explicit arguments in the rewrite, as described
above; replace the source imports by the statement module and the published
M131.002 proof module; omit the source `noncomputable section`,
`open Filter` and all other source declarations. The theorem name,
docstring, telescope and the rewrite sequence are otherwise unchanged. The
partition records no patch10 change to this module.

## Imports

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.QuotientAlgebraStatements`
  supplies the target and, through its imports, the published
  `principalUnits` definition and Mathlib's subgroup API.
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Proofs`
  supplies the published theorem `mem_principalUnits_iff`.

Both imported modules and everything they import are left unchanged.

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
other worker's draft is reused. The statement is Worker 211's and the
M131.002 proof Worker 229's, both used unchanged.

This module proves only the stated membership criterion.

## Development check

The project Lean service compiled this module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings; the
theorem has level parameter `u` and uses only `propext`, `Classical.choice`
and `Quot.sound`. This is a development check, not exact-target validation
or independent acceptance.
