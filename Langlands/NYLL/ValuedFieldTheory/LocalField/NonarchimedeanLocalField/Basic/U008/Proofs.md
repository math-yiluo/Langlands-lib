# Normalized valuation of natural powers

This module proves the theorem
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_pow`.
Its type is the already published proposition
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_powStatement`
at the universe level `u`:

```lean
theorem v_pow : v_powStatement.{u}
```

This is the proof phase of M128.008 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m128).

## Target and binders

By its definition in the published `Basic.PowValuationStatements` module,
`v_powStatement.{u}` is the closed proposition

```lean
∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (x : Kˣ) (n : Nat),
  v K (Additive.ofMul (x ^ n)) = (n : Int) * v K (Additive.ofMul x)
```

The binders are exactly the source theorem's, in source order:

| Binder | Kind | Meaning |
| --- | --- | --- |
| `K : Type u` | explicit | The field |
| `[Field K]` | instance | Its field structure |
| `[ValuativeRel K]` | instance | Its valuative relation, which determines `ValuativeRel.valuation K` |
| `[TopologicalSpace K]` | instance | Its topology |
| `[IsNonarchimedeanLocalField K]` | instance | Mathlib's class of nonarchimedean local fields |
| `x : Kˣ` | explicit | A field unit |
| `n : Nat` | explicit | The exponent |

`v K : Additive Kˣ → Int` is the published normalized integer valuation from
`Basic.Definitions` (M128.001): the additive exponent of the nonzero part of
the field valuation of a unit, transported along Mathlib's order isomorphism
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K` onto
`WithZero (Multiplicative Int)`. The statement says that the `n`-th power of a
unit (the monoid power in `Kˣ`) has `n` times its normalized valuation, the
product being taken in `Int` after casting `n`. No hypothesis is added.

## Imports and dependencies

The module has three direct imports, all published Library modules used
unchanged:

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.PowValuationStatements`,
  which defines the target `v_powStatement` (and imports `Basic.Definitions`,
  which supplies `v`);
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U004.Proofs`,
  which provides the published theorem
  `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_mul : v_mulStatement`
  (M128.004), i.e. for all `K` and units `x y`,
  `v K (Additive.ofMul (x * y)) = v K (Additive.ofMul x) + v K (Additive.ofMul y)`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U005.Proofs`,
  which provides the published theorem
  `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_one : v_oneStatement`
  (M128.005), i.e. for all `K`, `v K (Additive.ofMul (1 : Kˣ)) = 0`.

These are exactly the two source theorems the source proof uses. Since both
proofs are in the Library, they are imported rather than reproved; this
module introduces no local copy of either. The rest is Mathlib
(`pow_zero`, `pow_succ`, `Nat.cast_zero`, `zero_mul`, `Nat.cast_add_one`,
the `ring` tactic).

## Implemented proof

```lean
intro K _ _ _ _ x n
induction n with
| zero =>
    rw [pow_zero, v_one K, Nat.cast_zero, zero_mul]
| succ n ih =>
    rw [pow_succ, v_mul K, ih]
    rw [show ((n + 1 : Nat) : Int) = (n : Int) + 1 from Nat.cast_add_one n]
    ring
```

1. `intro K _ _ _ _ x n` introduces the seven binders of the statement.
2. Induction on `n`.
3. Base case `n = 0`: `pow_zero` rewrites `x ^ 0` to `1`, the published
   `v_one K` rewrites `v K (Additive.ofMul 1)` to `0`, and `Nat.cast_zero`
   and `zero_mul` turn the right-hand side `((0 : Nat) : Int) * v K (ofMul x)`
   into `0`, closing the goal `0 = 0` by reflexivity.
4. Successor case, with induction hypothesis
   `ih : v K (ofMul (x ^ n)) = n * v K (ofMul x)`: `pow_succ` rewrites
   `x ^ (n + 1)` to `x ^ n * x`, the published `v_mul K` splits its
   valuation into `v K (ofMul (x ^ n)) + v K (ofMul x)`, and `ih` replaces
   the first summand. Then the cast `((n + 1 : Nat) : Int)` is rewritten to
   `(n : Int) + 1` by `Nat.cast_add_one`, and `ring` proves
   `n * v K (ofMul x) + v K (ofMul x) = (n + 1) * v K (ofMul x)`.

Here `v_one K` and `v_mul K` are the published closed propositions applied to
the field `K`; their instance binders are filled by the instances introduced
in step 1.

The development check with `lean_check` in the approved environment compiled
the module with no diagnostics. Its inspection reports that `v_pow` is a
theorem with the single level parameter `u` and depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`. This check does not establish
independent semantic acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`,
lines 112–122](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean#L112-L122):
the docstring at line 112, the theorem signature at 113–115 and the proof at
116–122. It lies in the `LocalFieldTheory` namespace and its
`noncomputable section`, in the inner `IsNonarchimedeanLocalField` namespace
whose `open scoped ValuativeRel WithZero` directive at line 23 is kept here.
The source proof is:

```lean
  induction n with
  | zero =>
      rw [pow_zero, v_one, Nat.cast_zero, zero_mul]
  | succ n ih =>
      rw [pow_succ, v_mul, ih]
      rw [show ((n + 1 : Nat) : Int) = (n : Int) + 1 from Nat.cast_add_one n]
      ring
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`;
it was read and its SHA-256 verified as
`c696d08952343a0f668340bac35e2485e74b52134b0e205a3a4dc0653f48d25e`,
the hash recorded in the partition.

| Original declaration | Adapted declaration in `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField` |
| --- | --- |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v_pow` (theorem) | `v_pow` (theorem), proving the published target |
| Same theorem's statement | Existing `v_powStatement` |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v_one` | Existing published `v_one` (imported, M128.005) |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v_mul` | Existing published `v_mul` (imported, M128.004) |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v` | Existing `v` |

Only the first row introduces a declaration here. Modifications by
Worker 105 on 14 November 2026 are:

- add the `Langlands.NYLL` namespace prefix and replace the source import
  `Mathlib.NumberTheory.LocalField.Basic` with the three Library imports
  listed above, which provide it transitively;
- give the theorem the published closed statement as its type and introduce
  its seven binders with `intro K _ _ _ _ x n` before the source induction;
- write the rewrites with the published closed propositions as `v_one K` and
  `v_mul K` instead of the source's bare `v_one` and `v_mul`. The source
  theorems take `K` explicitly, so their bare names in `rw` are
  instantiated by unification; the published theorems are closed
  propositions whose leading binder is `K`, and supplying `K` gives the same
  rewrite rules;
- omit the source `noncomputable section`, which a theorem does not need, and
  all other source declarations.

The theorem name, docstring, the induction structure and every other rewrite
and the final `ring` are kept verbatim. The partition records no patch10
change to this original module.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
Additional attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Searches of the Library, staging and shared drafts for `v_pow` found no
earlier proof port of this theorem.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`,
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

## Attribution and boundary

The original copyright and author header is preserved verbatim:
copyright 2026 Naganori Yamaguchi, author “Naganori Yamaguchi (assisted
by OpenAI Codex)”, released under Apache-2.0. The Lean file carries the
dated modification record. Worker 105 adapted this proof directly from
the pinned original and wrote this companion. No other project worker
supplied code or a reused draft for this proof. The published
`Basic.Definitions`, `Basic.PowValuationStatements`, `Basic.U004.Proofs` and
`Basic.U005.Proofs` modules, all other imported Library modules and their
paired Markdown are used unchanged.

The unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are included in
`repository_paths` and are byte-identical to the retained originals.
Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No Mathlib code is copied into this file.

This module proves only M128.008. It publishes no second declaration named
`v_mul`, `v_one` or `v_zpow`; the integral-power theorem M128.009 is a
separate proof that imports this one.
