# Evaluation of the bundled valuation map

This module proves the theorem
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_apply`.
Its type is the already published proposition
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_applyStatement`
at the universe level `u`:

```lean
theorem valuationMap_apply : valuationMap_applyStatement.{u}
```

This is the proof phase of M134.004 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m134).

## Target and binders

By its definition in the published `ValuationExactSequence.EvaluationStatements`
module, `valuationMap_applyStatement.{u}` is the closed proposition

```lean
∀ (K : Type u) [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : Additive Kˣ),
  valuationMap K x = v K x
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

`valuationMap K : Additive Kˣ →+ Int` is the published additive homomorphism
from `ValuationExactSequence.Definitions` (M134.002),
`MonoidHom.toAdditive (valuationUnitsMulHom K)`. The multiplicative map
`valuationUnitsMulHom K : Kˣ →* Multiplicative Int` (M134.001) composes
`Units.map` of the field valuation, `Units.map` of Mathlib's order
isomorphism `IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K` onto
`ℤᵐ⁰ = WithZero (Multiplicative Int)`, and
`WithZero.unitsWithZeroEquiv`. `v K : Additive Kˣ → Int` is the published
unbundled normalized integer valuation from `Basic.Definitions` (M128.001).
The statement says that the bundled map and the unbundled function agree at
every unit. No hypothesis is added.

The sole direct import is the published
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.EvaluationStatements`
module. It imports the published `ValuationExactSequence.Definitions` and
`Basic.Definitions` modules, which supply `valuationMap` and `v`. No proof
module is imported.

## Implemented proof

```lean
intro K _ _ _ _ x
rfl
```

1. `intro K _ _ _ _ x` introduces the six binders of the statement.
2. `rfl` closes the equation by definitional unfolding. Applied to `x`, the
   additive form of `valuationUnitsMulHom K` is the image of the unit
   `Additive.toMul x` under that monoid homomorphism, read in `Int`. Mapping
   `x` first by the valuation and then by `valueGroupWithZeroIsoInt K` gives
   a unit of `ℤᵐ⁰` whose value is the transported valuation of `x`, and
   `WithZero.unitsWithZeroEquiv` sends a unit `a` to `WithZero.unzero
   a.ne_zero` (`Mathlib/Algebra/GroupWithZero/WithZero.lean`, lines
   295–296). So the result is `WithZero.unzero` of the transported valuation
   of `x`; its nonvanishing proof differs from the one in `v`, but proofs of
   the same proposition are definitionally equal. Reading the result in
   `Int` is `Multiplicative.toAdd`, which gives the body of `v K x`.

The development check reports that the theorem has the single level
parameter `u` and compiled with no diagnostics.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean`,
lines 51–56](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean#L51-L56):
the theorem signature at 51–53, the proof `rfl` at 54 and a blank line at
55; line 56 is the docstring of the next theorem. The docstring of
`valuationMap_apply` is at lines 48–49 and its `@[simp]` attribute at line
50, just before the partition's start line. It lies in the `LocalFieldTheory`
namespace and its `noncomputable section`, in the inner
`IsNonarchimedeanLocalField` namespace whose
`open scoped ValuativeRel WithZero` directive is kept here. The complete
original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean`;
it was read and its SHA-256 verified as
`8a8515596e4388771957f2c4c484e8c86767236ab79f973fa405df2d34e02908`,
the hash recorded in the partition.

| Original declaration | Adapted declaration in `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField` |
| --- | --- |
| `LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_apply` (theorem) | `valuationMap_apply` (theorem), proving the published target |
| Same theorem's statement | Existing `valuationMap_applyStatement` |
| `LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap`, `v` | Existing `valuationMap`, `v` |

Only the first row introduces a declaration here. Modifications by
Worker 120 on 13 November 2026 are:

- add the `Langlands.NYLL` namespace prefix and replace the source imports
  with the sole EvaluationStatements import;
- give the theorem the published closed statement as its type and introduce
  its six binders with `intro K _ _ _ _ x` before the original `rfl`;
- omit the `@[simp]` attribute. The theorem's type is the statement
  constant, not a syntactic equation, so it would not give the source simp
  lemma;
- shorten the docstring. The source docstring repeats the same sentence
  twice; the adapted docstring keeps it once;
- omit the source `noncomputable section`, which a theorem does not need, and
  all other source declarations.

The theorem name and the proof `rfl` are kept. The partition records no
patch10 change to this original module.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
Additional attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No NYLL or local-field valuation erratum was found in the Library errata
notes. Searches of staging and shared drafts for `valuationMap_apply` found
no earlier proof port of this theorem.

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
`Basic.Definitions`, `ValuationExactSequence.Definitions` and
`ValuationExactSequence.EvaluationStatements` modules, all other imported
Library modules and their paired Markdown are used unchanged.

The unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are included in
`repository_paths` and are byte-identical to the retained originals.
Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No Mathlib code is copied into this file.

This module proves only M134.004. It does not prove any other M134 theorem.
