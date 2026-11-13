# Surjectivity of the normalized valuation

This module proves the theorem
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_surjective`.
Its type is the already published proposition
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_surjectiveStatement`
at the universe level `u`:

```lean
theorem v_surjective : v_surjectiveStatement.{u}
```

This is the proof phase of M128.003 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m128).

## Target and binders

By its definition in the published `Basic.ValuationStatements` module,
`v_surjectiveStatement.{u}` is the closed proposition

```lean
∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K],
  Function.Surjective (v K)
```

The binders are exactly the source theorem's, in source order:

| Binder | Kind | Meaning |
| --- | --- | --- |
| `K : Type u` | explicit | The field |
| `[Field K]` | instance | Its field structure |
| `[ValuativeRel K]` | instance | Its valuative relation, which determines `ValuativeRel.valuation K` |
| `[TopologicalSpace K]` | instance | Its topology |
| `[IsNonarchimedeanLocalField K]` | instance | Mathlib's class of nonarchimedean local fields |

`v K : Additive Kˣ → Int` is the published normalized integer valuation from
`Basic.Definitions` (M128.001). For a unit `x`, it transports the value
`ValuativeRel.valuation K x` along Mathlib's order isomorphism
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K` from the value group
with zero to `ℤᵐ⁰ = WithZero (Multiplicative Int)`, removes the zero with
`WithZero.unzero` (the value is nonzero because `x` is a unit), and takes the
additive exponent with `Multiplicative.toAdd`. The statement says that every
integer is such a valuation. No hypothesis is added.

The sole direct import is the published
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.ValuationStatements`
module. It imports the published `Basic.Definitions` module, which supplies
`v`, and the published `Basic.U016.Definitions` module, which supplies
`integerUnitsToFieldUnits` and is not used here. No other M128 proof is used.

## Implemented proof

```lean
intro K _ _ _ _ n
let γ : ValuativeRel.ValueGroupWithZero K :=
  (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).symm
    ((Multiplicative.ofAdd n : Multiplicative Int) : WithZero (Multiplicative Int))
obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective γ
have hγ_ne : γ ≠ 0 := by
  exact (map_ne_zero
    (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).symm).2 WithZero.coe_ne_zero
have ha0 : a ≠ 0 := by
  intro h
  apply hγ_ne
  simpa [h] using ha.symm
refine ⟨Additive.ofMul (Units.mk0 a ha0), ?_⟩
simp [v, γ, ha]
```

1. `intro K _ _ _ _ n` introduces the five binders of the statement and,
   since `Function.Surjective (v K)` unfolds to `∀ n, ∃ x, v K x = n`, the
   integer `n` that the source proof introduces with its own `intro n`.
2. `γ` is the element of the value group with zero corresponding to
   `ofAdd n` under the inverse of `valueGroupWithZeroIsoInt K`.
3. `ValuativeRel.valuation_surjective`
   (`Mathlib/RingTheory/Valuation/ValuativeRel/Basic.lean`, line 993) states
   that the valuation of a division ring with a valuative relation is
   surjective onto its value group with zero. It gives `a : K` with
   `ha : ValuativeRel.valuation K a = γ`.
4. `hγ_ne`: `γ` is nonzero, because the inverse isomorphism is injective and
   zero-preserving (`map_ne_zero`), and the coercion of `ofAdd n` into
   `WithZero` is nonzero (`WithZero.coe_ne_zero`).
5. `ha0`: `a` is nonzero, for otherwise rewriting `ha.symm` with `h` and
   the simp lemma `map_zero` would give `γ = 0`.
6. The witness is the unit `Units.mk0 a ha0`, viewed additively. A
   development `simp?` check reports that `simp [v, γ, ha]` uses exactly
   `v`, `toMul_ofMul`, `Units.val_mk0`, `ha`,
   `OrderMonoidIso.apply_symm_apply`, `WithZero.unzero_coe`, `toAdd_ofAdd`
   and `γ`: after unfolding `v`, the unit's underlying element is `a`, its
   valuation is `γ` by `ha`, applying `valueGroupWithZeroIsoInt K` to
   `γ` undoes the inverse, removing the zero from the coercion of `ofAdd n`
   gives `ofAdd n`, and `toAdd (ofAdd n) = n`.

The development check reports that the theorem has the single level
parameter `u` and uses only `propext`, `Classical.choice` and `Quot.sound`,
all already used by the imported definitions and Mathlib; the proof adds no
further axiom.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`,
lines 54–72](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean#L54-L72):
the theorem signature at 54–56, the proof at 57–70 and a blank line at 71;
line 72 is the docstring of the next theorem. The docstring of
`v_surjective` is at line 53, just before the partition's start line. It lies in the `LocalFieldTheory` namespace and its
`noncomputable section`, in the inner `IsNonarchimedeanLocalField` namespace
whose `open scoped ValuativeRel WithZero` directive at line 23 is kept here.
The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`;
it was read and its SHA-256 verified as
`c696d08952343a0f668340bac35e2485e74b52134b0e205a3a4dc0653f48d25e`,
the hash recorded in the partition.

| Original declaration | Adapted declaration in `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField` |
| --- | --- |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v_surjective` (theorem) | `v_surjective` (theorem), proving the published target |
| Same theorem's statement | Existing `v_surjectiveStatement` |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v` | Existing `v` |

Only the first row introduces a declaration here. Modifications by
Worker 120 on 13 November 2026 are:

- add the `Langlands.NYLL` namespace prefix and replace the source import
  `Mathlib.NumberTheory.LocalField.Basic` with the sole ValuationStatements
  import, which provides it transitively;
- give the theorem the published closed statement as its type; the source's
  binders, together with the integer `n`, are introduced by the single
  `intro K _ _ _ _ n`, which replaces the source's `intro n`;
- omit the source `noncomputable section`, which a theorem does not need, and
  all other source declarations.

The theorem name, docstring and every proof step after the introduction are
kept verbatim. The partition records no patch10 change to this original
module.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
Additional attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No NYLL or local-field valuation erratum was found in the Library errata
notes. Searches of staging and shared drafts for `v_surjective` found no
earlier proof port of this theorem.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`,
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. A
development check compiled the module with no diagnostics. This check does
not establish independent semantic acceptance or Integrator publication.

## Attribution and boundary

The original copyright and author header is preserved verbatim:
copyright 2026 Naganori Yamaguchi, author “Naganori Yamaguchi (assisted
by OpenAI Codex)”, released under Apache-2.0. The Lean file carries the
dated modification record. Worker 120 adapted this proof directly from
the pinned original and wrote this companion. No other project worker
supplied code or a reused draft for this proof. The published
`Basic.Definitions`, `Basic.U016.Definitions` and `Basic.ValuationStatements`
modules, all other imported Library modules and their paired Markdown are
used unchanged.

The unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are included in
`repository_paths` and are byte-identical to the retained originals.
Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No Mathlib code is copied into this file.

This module proves only M128.003. It does not prove any other M128 theorem,
nor the surjectivity of the bundled map `valuationMap` (M134.005).
