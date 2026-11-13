# Normalized valuation of an inverse

This module proves the theorem
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_inv`.
Its type is the already published proposition
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_invStatement`
at the universe level `u`:

```lean
theorem v_inv : v_invStatement.{u}
```

This is the proof phase of M128.006 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m128).

## Target and binders

By its definition in the published `Basic.ValuationStatements` module,
`v_invStatement.{u}` is the closed proposition

```lean
∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (x : Kˣ),
  v K (Additive.ofMul x⁻¹) = -v K (Additive.ofMul x)
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

`v K : Additive Kˣ → Int` is the published normalized integer valuation from
`Basic.Definitions` (M128.001): the additive exponent
(`Multiplicative.toAdd`) of the nonzero part (`WithZero.unzero`) of the field
valuation of a unit, transported along Mathlib's order isomorphism
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K` onto
`ℤᵐ⁰ = WithZero (Multiplicative Int)`. The statement says that the inverse
unit has the negated normalized valuation. No hypothesis is added.

The sole direct import is the published
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.ValuationStatements`
module. It imports the published `Basic.Definitions` module, which supplies
`v`, and the published `Basic.U016.Definitions` module, which is not used
here. The source proof uses the theorems `v_mul` (M128.004) and `v_one`
(M128.005). No proof of either is in the Library at this workspace's base,
so no proof module is imported; both facts are proved locally, as described
below.

## Implemented proof

```lean
intro K _ _ _ _ x
-- The source theorem `v_mul K` (M128.004), proved by its original `simp` call.
have hmulGen : ∀ a b : Kˣ,
    v K (Additive.ofMul (a * b)) =
      v K (Additive.ofMul a) + v K (Additive.ofMul b) := by
  intro a b
  simp [v, Valuation.map_mul, WithZero.unzero_mul, toAdd_mul]
have hmul := hmulGen x x⁻¹
-- The source proof of `v_one K` (M128.005), inlined.
have hone : v K (Additive.ofMul (1 : Kˣ)) = 0 := by
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
rw [mul_inv_cancel, hone] at hmul
omega
```

1. `intro K _ _ _ _ x` introduces the six binders of the statement.
2. `hmulGen` is the statement of the source theorem `v_mul K` for arbitrary
   units `a b`, proved by the source's `simp` call for `v_mul` (unfold `v`,
   then use multiplicativity of the valuation and of the order isomorphism,
   `WithZero.unzero_mul` and `toAdd_mul`). `hmul` specializes it to `x` and
   `x⁻¹`, exactly the source's `v_mul K x x⁻¹`. The general form is needed:
   proving the specialized equation directly by the same `simp` call fails,
   because `simp` first rewrites `x * x⁻¹` to `1` and is then left with an
   equation it cannot close.
3. `hone` is the source theorem `v_one K`, proved by the source proof of
   `v_one`, copied verbatim: after `dsimp [v]`, the nonzero part of the
   transported valuation of `1` is computed to be `1` by injectivity of the
   coercion into `WithZero` and `map_one`, and `toAdd_one` finishes.
4. `rw [mul_inv_cancel, hone] at hmul` rewrites `x * x⁻¹` to `1` and then
   `v K (ofMul 1)` to `0`, so `hmul` becomes
   `0 = v K (ofMul x) + v K (ofMul x⁻¹)`, an equation in `Int`.
5. `omega` derives the goal `v K (ofMul x⁻¹) = -v K (ofMul x)` from it,
   treating the two valuations as integer atoms.

The development check reports that the theorem has the single level
parameter `u` and compiled with no diagnostics.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`,
lines 98–105](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean#L98-L105):
the theorem signature at 98–100, the proof at 101–103 and a blank line at
104; line 105 is the docstring of the next theorem. The docstring of `v_inv`
is at line 97, just before the partition's start line. The inlined
prerequisites are the proof of `v_mul` at line 77 (signature at 73–76) and
the proof of `v_one` at lines 84–95 (signature at 81–83) of the same file.
All lie in the `LocalFieldTheory` namespace and its `noncomputable section`,
in the inner `IsNonarchimedeanLocalField` namespace whose
`open scoped ValuativeRel WithZero` directive at line 23 is kept here.
The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`;
it was read and its SHA-256 verified as
`c696d08952343a0f668340bac35e2485e74b52134b0e205a3a4dc0653f48d25e`,
the hash recorded in the partition.

| Original declaration | Adapted declaration in `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField` |
| --- | --- |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v_inv` (theorem) | `v_inv` (theorem), proving the published target |
| Same theorem's statement | Existing `v_invStatement` |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v_mul K` | Local fact `hmulGen` inside the proof; no declaration |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v_one K` | Local fact `hone` inside the proof; no declaration |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v` | Existing `v` |

Only the first row introduces a declaration here. Modifications by
Worker 120 on 13 November 2026 are:

- add the `Langlands.NYLL` namespace prefix and replace the source import
  `Mathlib.NumberTheory.LocalField.Basic` with the sole ValuationStatements
  import, which provides it transitively;
- give the theorem the published closed statement as its type and introduce
  its six binders with `intro K _ _ _ _ x`;
- replace the source term `v_mul K x x⁻¹` by the local fact `hmulGen`,
  proved by the source proof of `v_mul` for all pairs of units, specialized
  to `x x⁻¹`; and replace the rewrite with `v_one` by a rewrite with the
  local fact `hone`, proved by the verbatim source proof of `v_one`. This is
  needed because no proof of M128.004 or M128.005 is in the Library. No
  second declaration named `v_mul` or `v_one` is published by this module;
- omit the source `noncomputable section`, which a theorem does not need, and
  all other source declarations.

The theorem name, docstring, the rewrite with `mul_inv_cancel` and the final
`omega` are kept. The partition records no patch10 change to this original
module.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
Additional attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No NYLL or local-field valuation erratum was found in the Library errata
notes. Searches of staging and shared drafts for `v_inv` found no earlier
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

This module proves only M128.006. It does not publish M128.004 or M128.005
as declarations, nor any other M128 theorem.
