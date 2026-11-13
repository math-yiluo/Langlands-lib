# Evaluation of the normalized valuation

This module proves the theorem
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_apply`.
Its type is the already published proposition
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_applyStatement`
at the universe level `u`:

```lean
theorem v_apply : v_applyStatement.{u}
```

This is the proof phase of M128.002 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m128).

## Target and binders

By its definition in the published `Basic.ValuationStatements` module,
`v_applyStatement.{u}` is the closed proposition

```lean
∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (x : Additive Kˣ),
  v K x =
    Multiplicative.toAdd
      (WithZero.unzero
        (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
          (ValuativeRel.valuation K ((Additive.toMul x : Kˣ) : K)))
        ((map_ne_zero (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).2
          ((Valuation.ne_zero_iff (ValuativeRel.valuation K)).2 (Additive.toMul x).ne_zero)))
```

The binders are exactly the source theorem's, in source order:

| Binder | Kind | Meaning |
| --- | --- | --- |
| `K : Type u` | explicit | The field |
| `[Field K]` | instance | Its field structure |
| `[ValuativeRel K]` | instance | Its valuative relation, which determines `ValuativeRel.valuation K` |
| `[TopologicalSpace K]` | instance | Its topology |
| `[IsNonarchimedeanLocalField K]` | instance | Mathlib's class of nonarchimedean local fields |
| `x : Additive Kˣ` | explicit | A field unit, written additively |

The left side is the published normalized integer valuation
`v K : Additive Kˣ → Int` from `Basic.Definitions` (M128.001) at `x`. The
right side transports the field valuation of the unit `x` along Mathlib's
order isomorphism `IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K`
onto `ℤᵐ⁰ = WithZero (Multiplicative Int)`, removes the zero with
`WithZero.unzero` (justified by the displayed nonvanishing proof), and takes
the additive exponent with `Multiplicative.toAdd`. No hypothesis is added.

The sole direct import is the published
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.ValuationStatements`
module. It imports the published `Basic.Definitions` module, which supplies
`v`, and the published `Basic.U016.Definitions` module, which is not used
here. No other M128 proof is used.

## Implemented proof

```lean
intro K _ _ _ _ x
rfl
```

1. `intro K _ _ _ _ x` introduces the six binders of the statement.
2. `rfl` closes the equation: the right side is, symbol for symbol, the
   body of the published definition of `v` applied to `x`, so the two sides
   are definitionally equal by unfolding `v` once.

The development check reports that the theorem has the single level
parameter `u` and compiled with no diagnostics.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`,
lines 42–53](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean#L42-L53):
the theorem signature at 42–50, the proof `rfl` at 51 and a blank line at
52; line 53 is the docstring of the next theorem. The docstring of `v_apply`
is at lines 39–40 and its `@[simp]` attribute at line 41, just before the
partition's start line. It lies in the `LocalFieldTheory` namespace and its
`noncomputable section`, in the inner `IsNonarchimedeanLocalField` namespace
whose `open scoped ValuativeRel WithZero` directive at line 23 is kept here.
The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`;
it was read and its SHA-256 verified as
`c696d08952343a0f668340bac35e2485e74b52134b0e205a3a4dc0653f48d25e`,
the hash recorded in the partition.

| Original declaration | Adapted declaration in `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField` |
| --- | --- |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v_apply` (theorem) | `v_apply` (theorem), proving the published target |
| Same theorem's statement | Existing `v_applyStatement` |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v` | Existing `v` |

Only the first row introduces a declaration here. Modifications by
Worker 120 on 13 November 2026 are:

- add the `Langlands.NYLL` namespace prefix and replace the source import
  `Mathlib.NumberTheory.LocalField.Basic` with the sole ValuationStatements
  import, which provides it transitively;
- give the theorem the published closed statement as its type and introduce
  its six binders with `intro K _ _ _ _ x` before the original `rfl`;
- omit the `@[simp]` attribute. The theorem's type is the statement
  constant, not a syntactic equation, so it would not give the source simp
  lemma;
- omit the source `noncomputable section`, which a theorem does not need, and
  all other source declarations.

The theorem name, docstring and the proof `rfl` are kept. The partition
records no patch10 change to this original module.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
Additional attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No NYLL or local-field valuation erratum was found in the Library errata
notes. Searches of staging and shared drafts for `v_apply` found no earlier
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

This module proves only M128.002. It does not prove any other M128 theorem.
