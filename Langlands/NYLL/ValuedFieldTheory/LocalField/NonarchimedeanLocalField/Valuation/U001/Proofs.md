# Membership in the valuation ring: exact proof

This module proves
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuation_integer_membership`
with exactly the closed type
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuation_integer_membershipStatement.{u}`.
Its universe parameter is `u`. The published statement module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Valuation.MembershipStatement`
is imported unchanged.

The proposition's complete internal telescope is

```lean
∀ (K : Type u) [Field K] [ValuativeRel K] (x : K),
  x ∈ 𝒪[K] ↔ ValuativeRel.valuation K x ≤ 1
```

Here `𝒪[K]` is Mathlib's scoped notation for
`Valuation.integer (ValuativeRel.valuation K)`, the subring of elements of
valuation at most one for the canonical valuation of the valuative relation.
The theorem has no topology or local-field hypothesis; the inherited
namespace `IsNonarchimedeanLocalField` introduces no such assumption.

## Implemented proof

After introducing `K`, its two structure instances and `x`, the proof is the
original source term

```lean
(Valuation.mem_integer_iff (ValuativeRel.valuation K) x).symm
```

Mathlib's `Valuation.mem_integer_iff` states, for a valuation `v` and an
element `r`, that `r ∈ v.integer ↔ v r ≤ 1`, and is proved by `rfl`: the
carrier of `v.integer` is `{x | v x ≤ 1}`, so the two sides are
definitionally the same proposition. With `v := ValuativeRel.valuation K`
and `r := x`, the source's `.symm` produces
`ValuativeRel.valuation K x ≤ 1 ↔ x ∈ 𝒪[K]`. The final `exact` accepts it
for the goal `x ∈ 𝒪[K] ↔ ValuativeRel.valuation K x ≤ 1` because Lean
checks the two `Iff` types up to definitional unfolding, and each side of
one is definitionally the corresponding side of the other. The source's
`.symm` is therefore harmless but not needed; it is kept unchanged.

## Source and correspondence

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Valuation.lean`,
SHA-256 `6cb16ae8fea982c7f08e7d0d321806fa318e6df81fcf6b9bec6d88e93e720d0e`.
It is available in registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement
is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Lines 1–40 were read; lines 28–34 contain the statement and proof of
M130.001 (the next unit, M130.002, starts at line 35).

The source theorem
`LocalFieldTheory.IsNonarchimedeanLocalField.valuation_integer_membership`
becomes the identically suffixed theorem in the `Langlands.NYLL` namespace.
This is the proof phase of M130.001 in
`notes/reuse/nyll-public-port/m121-m144.md`. The proof term is unchanged;
only the closed target's telescope is introduced first.

Worker 135 made these changes on 14 November 2026:

- Prefix the namespace with `Langlands.NYLL`.
- State the theorem with the published closed proposition as its entire type,
  preserving universe `.{u}` and the binder order and kinds, introduce that
  telescope with `intro`, and give the source term with `exact`.
- Omit all other declarations of the original file, its
  `noncomputable section`, its `universe` declaration and the unused
  `open DiscreteValuationField`.
- Replace the original imports by the single import below.
- Retain the original copyright, license and author header and add the
  modification comment and this paired explanation.

## Actual imports

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Valuation.MembershipStatement`
  supplies the exact published target and, through its import
  `Mathlib.Topology.Algebra.Valued.ValuativeRel`, the valuation-ring notation
  and `Valuation.mem_integer_iff`.

The original imports, NYLL `DiscreteValuationField.FieldNorm` and
`NonarchimedeanLocalField.Norm`, are unnecessary for this proof. No NYLL
declaration is used.

## Development check

In environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), the module compiled
with no errors or warnings. Declaration inspection reports a theorem with
level parameters `[u]` and only `propext`, `Classical.choice` and
`Quot.sound`. This development check is separate from candidate
exact-target validation and independent semantic review.

## Attribution

The retained original header credits Naganori Yamaguchi (assisted by OpenAI
Codex) and releases the source under Apache-2.0. The unchanged upstream
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are already published.
Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No other worker's unpublished draft was reused.
