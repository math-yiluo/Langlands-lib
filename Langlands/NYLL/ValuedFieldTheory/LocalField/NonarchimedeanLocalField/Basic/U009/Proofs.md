# Normalized valuation of integral powers

This module proves the theorem
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_zpow`.
Its type is the already published proposition
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_zpowStatement`
at the universe level `u`:

```lean
theorem v_zpow : v_zpowStatement.{u}
```

This is the proof phase of M128.009 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m128).

## Target and binders

By its definition in the published `Basic.PowValuationStatements` module,
`v_zpowStatement.{u}` is the closed proposition

```lean
∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (x : Kˣ) (n : Int),
  v K (Additive.ofMul (x ^ n)) = n * v K (Additive.ofMul x)
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
| `n : Int` | explicit | The exponent |

`v K : Additive Kˣ → Int` is the published normalized integer valuation from
`Basic.Definitions` (M128.001): the additive exponent of the nonzero part of
the field valuation of a unit, transported along Mathlib's order isomorphism
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K` onto
`WithZero (Multiplicative Int)`. Here `x ^ n` is the integer power in the
group `Kˣ` (so `x ^ (-1) = x⁻¹`), and the statement says that it has `n`
times the normalized valuation of `x`. No hypothesis is added.

## Imports and dependencies

The module has three direct imports, all published Library modules used
unchanged:

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.PowValuationStatements`,
  which defines the target `v_zpowStatement` (and imports `Basic.Definitions`,
  which supplies `v`);
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U006.Proofs`,
  which provides the published theorem
  `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_inv : v_invStatement`
  (M128.006), i.e. for all `K` and units `x`,
  `v K (Additive.ofMul x⁻¹) = -v K (Additive.ofMul x)`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U008.Proofs`,
  which provides the published theorem
  `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_pow : v_powStatement`
  (M128.008), i.e. for all `K`, units `x` and `n : Nat`,
  `v K (Additive.ofMul (x ^ n)) = (n : Int) * v K (Additive.ofMul x)`.

These are exactly the two source theorems the source proof uses. Both proofs
are in the Library, so they are imported rather than reproved; this module
introduces no local copy of either. The rest is Mathlib and core Lean
(`zpow_negSucc`, the `simp` set used by `simpa`, the `ring` tactic).

## Implemented proof

```lean
intro K _ _ _ _ x n
cases n with
| ofNat n =>
    simpa using v_pow K x n
| negSucc n =>
    rw [zpow_negSucc, v_inv K, v_pow K]
    change -(((n + 1 : Nat) : Int) * v K (Additive.ofMul x)) =
      (-(((n + 1 : Nat) : Int))) * v K (Additive.ofMul x)
    ring
```

1. `intro K _ _ _ _ x n` introduces the seven binders of the statement.
2. `cases n` splits the integer exponent into its two constructors
   `Int.ofNat n` (nonnegative) and `Int.negSucc n` (the integer `-(n + 1)`),
   for `n : Nat`.
3. Case `Int.ofNat n`: the goal is
   `v K (ofMul (x ^ Int.ofNat n)) = Int.ofNat n * v K (ofMul x)`.
   `simpa using v_pow K x n` simplifies both this goal and the published
   natural-power equation
   `v_pow K x n : v K (ofMul (x ^ n)) = (n : Int) * v K (ofMul x)` with the
   default `simp` set and closes the goal once the two simplified forms
   agree. The relevant simp lemmas identify the nonnegative integer
   exponent with the natural one: core `Int.ofNat_eq_natCast` rewrites
   `Int.ofNat n` to the cast `(n : Int)`, and Mathlib's simp lemmas for powers
   (such as `zpow_natCast`, or `ofMul_zpow`, `ofMul_pow` and `natCast_zsmul`
   inside `Additive.ofMul`) identify the integer power by `(n : Int)` with
   the natural power by `n`. The exact intermediate normal form is not
   recorded here; the development check confirms that `simpa` closes the
   case.
4. Case `Int.negSucc n`: Mathlib's `zpow_negSucc` rewrites
   `x ^ Int.negSucc n` to `(x ^ (n + 1))⁻¹`; the published `v_inv K` turns
   the valuation of this inverse into `-v K (ofMul (x ^ (n + 1)))`; and the
   published `v_pow K` (at the natural exponent `n + 1`) turns that into
   `-(((n + 1 : Nat) : Int) * v K (ofMul x))`. The `change` step restates
   the right-hand side `Int.negSucc n * v K (ofMul x)` as
   `(-(((n + 1 : Nat) : Int))) * v K (ofMul x)`, which is definitionally the
   same integer, and `ring` proves `-(a * b) = (-a) * b`.

Here `v_inv K` and `v_pow K` are the published closed propositions applied to
the field `K`; their instance binders are filled by the instances introduced
in step 1.

The development check with `lean_check` in the approved environment compiled
the module with no diagnostics. Its inspection reports that `v_zpow` is a
theorem with the single level parameter `u` and depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`. This check does not establish
independent semantic acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`,
lines 124–136](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean#L124-L136):
the docstring at lines 124–125, the theorem signature at 126–128 and the
proof at 129–136. It lies in the `LocalFieldTheory` namespace and its
`noncomputable section`, in the inner `IsNonarchimedeanLocalField` namespace
whose `open scoped ValuativeRel WithZero` directive at line 23 is kept here.
The source proof is:

```lean
  cases n with
  | ofNat n =>
      simpa using v_pow K x n
  | negSucc n =>
      rw [zpow_negSucc, v_inv, v_pow]
      change -(((n + 1 : Nat) : Int) * v K (Additive.ofMul x)) =
        (-(((n + 1 : Nat) : Int))) * v K (Additive.ofMul x)
      ring
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`;
it was read and its SHA-256 verified as
`c696d08952343a0f668340bac35e2485e74b52134b0e205a3a4dc0653f48d25e`,
the hash recorded in the partition.

| Original declaration | Adapted declaration in `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField` |
| --- | --- |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v_zpow` (theorem) | `v_zpow` (theorem), proving the published target |
| Same theorem's statement | Existing `v_zpowStatement` |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v_pow` | Existing published `v_pow` (imported, M128.008) |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v_inv` | Existing published `v_inv` (imported, M128.006) |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v` | Existing `v` |

Only the first row introduces a declaration here. Modifications by
Worker 105 on 14 November 2026 are:

- add the `Langlands.NYLL` namespace prefix and replace the source import
  `Mathlib.NumberTheory.LocalField.Basic` with the three Library imports
  listed above, which provide it transitively;
- give the theorem the published closed statement as its type and introduce
  its seven binders with `intro K _ _ _ _ x n` before the source case split;
- write the rewrites with the published closed propositions as `v_inv K` and
  `v_pow K` instead of the source's bare `v_inv` and `v_pow`. The source
  theorems take `K` explicitly, so their bare names in `rw` are
  instantiated by unification; the published theorems are closed
  propositions whose leading binder is `K`, and supplying `K` gives the same
  rewrite rules. The source term `v_pow K x n` in the first case is kept
  verbatim;
- state the docstring sentence once: the source docstring (lines 124–125)
  repeats the same sentence twice;
- omit the source `noncomputable section`, which a theorem does not need, and
  all other source declarations.

The theorem name, the case split, the `simpa` call, the rewrite with
`zpow_negSucc`, the `change` step and the final `ring` are kept verbatim.
The partition records no patch10 change to this original module.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
Additional attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Searches of the Library, staging and shared drafts for `v_zpow` found no
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
`Basic.Definitions`, `Basic.PowValuationStatements`, `Basic.U006.Proofs` and
`Basic.U008.Proofs` modules, all other imported Library modules and their
paired Markdown are used unchanged.

The unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are included in
`repository_paths` and are byte-identical to the retained originals.
Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No Mathlib code is copied into this file.

This module proves only M128.009. It publishes no second declaration named
`v_pow` or `v_inv`.
