# Normalized valuation of one

This module proves the theorem
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_one`.
Its type is the already published proposition
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_oneStatement`
at the universe level `u`:

```lean
theorem v_one : v_oneStatement.{u}
```

This is the proof phase of M128.005 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m128).

## Target and binders

By its definition in the published `Basic.ValuationStatements` module,
`v_oneStatement.{u}` is the closed proposition

```lean
∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K],
  v K (Additive.ofMul (1 : Kˣ)) = 0
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
`Basic.Definitions` (M128.001): the additive exponent
(`Multiplicative.toAdd`) of the nonzero part (`WithZero.unzero`) of the field
valuation of a unit, transported along Mathlib's order isomorphism
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K` onto
`ℤᵐ⁰ = WithZero (Multiplicative Int)`. The statement says that the unit one
has normalized valuation zero. No hypothesis is added.

The sole direct import is the published
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.ValuationStatements`
module. It imports the published `Basic.Definitions` module, which supplies
`v`, and the published `Basic.U016.Definitions` module, which is not used
here. No other M128 proof is used.

## Implemented proof

```lean
intro K _ _ _ _
dsimp [v]
have hunzero :
    WithZero.unzero
      (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
        (ValuativeRel.valuation K (((1 : Kˣ) : K))))
      ((map_ne_zero (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).2
        ((Valuation.ne_zero_iff (ValuativeRel.valuation K)).2 (Units.ne_zero (1 : Kˣ)))) =
      (1 : Multiplicative Int) := by
  apply WithZero.coe_injective
  simp only [WithZero.coe_unzero, Units.val_one, map_one, WithZero.coe_one]
rw [hunzero]
exact toAdd_one
```

1. `intro K _ _ _ _` introduces the five binders of the statement.
2. `dsimp [v]` unfolds `v` and simplifies `Additive.toMul (Additive.ofMul 1)`
   to `1`, leaving `Multiplicative.toAdd (WithZero.unzero …) = 0`, where the
   argument of `unzero` is the transported valuation of `((1 : Kˣ) : K)`.
3. `hunzero` computes that nonzero part. By injectivity of the coercion
   `Multiplicative Int → WithZero (Multiplicative Int)`
   (`WithZero.coe_injective`), it suffices to compare coercions:
   `WithZero.coe_unzero` replaces the coerced nonzero part by the
   transported valuation itself, `Units.val_one` makes the underlying field
   element `1`, `map_one` (for the valuation and then for the order
   isomorphism) makes the value `1`, and `WithZero.coe_one` matches it with
   the coercion of `1`.
4. `rw [hunzero]` turns the goal into `Multiplicative.toAdd 1 = 0`, which is
   `toAdd_one`.

The development check reports that the theorem has the single level
parameter `u` and compiled with no diagnostics.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`,
lines 81–97](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean#L81-L97):
the theorem signature at 81–83, the proof at 84–95 and a blank line at 96;
line 97 is the docstring of the next theorem. The docstring of `v_one` is at
line 79 and its `@[simp]` attribute at line 80, just before the partition's
start line. It lies in the `LocalFieldTheory` namespace and its
`noncomputable section`, in the inner `IsNonarchimedeanLocalField` namespace
whose `open scoped ValuativeRel WithZero` directive at line 23 is kept here.
The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`;
it was read and its SHA-256 verified as
`c696d08952343a0f668340bac35e2485e74b52134b0e205a3a4dc0653f48d25e`,
the hash recorded in the partition.

| Original declaration | Adapted declaration in `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField` |
| --- | --- |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v_one` (theorem) | `v_one` (theorem), proving the published target |
| Same theorem's statement | Existing `v_oneStatement` |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v` | Existing `v` |

Only the first row introduces a declaration here. Modifications by
Worker 120 on 13 November 2026 are:

- add the `Langlands.NYLL` namespace prefix and replace the source import
  `Mathlib.NumberTheory.LocalField.Basic` with the sole ValuationStatements
  import, which provides it transitively;
- give the theorem the published closed statement as its type and introduce
  its five binders with `intro K _ _ _ _` before the original proof;
- omit the `@[simp]` attribute. The theorem's type is the statement
  constant, not a syntactic equation, so it would not give the source simp
  lemma;
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
notes. Searches of staging and shared drafts for `v_one` found no earlier
proof port of this theorem.

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

This module proves only M128.005. It does not prove any other M128 theorem.
