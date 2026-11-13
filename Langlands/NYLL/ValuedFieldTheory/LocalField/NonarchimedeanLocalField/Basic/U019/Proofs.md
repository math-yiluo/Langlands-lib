# Normalized valuation of integral units

This module proves the theorem
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_integerUnitsToFieldUnits`.
Its type is the already published proposition
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_integerUnitsToFieldUnitsStatement`
at the universe level `u`:

```lean
theorem v_integerUnitsToFieldUnits : v_integerUnitsToFieldUnitsStatement.{u}
```

This is the proof phase of M128.019 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m128).

## Target and binders

By its definition in the published `Basic.ValuationStatements` module,
`v_integerUnitsToFieldUnitsStatement.{u}` is the closed proposition

```lean
∀ (K : Type u) [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : 𝒪[K]ˣ),
  v K (Additive.ofMul (integerUnitsToFieldUnits K x)) = 0
```

The binders are exactly the source theorem's, in source order:

| Binder | Kind | Meaning |
| --- | --- | --- |
| `K : Type u` | explicit | The field |
| `[Field K]` | instance | Its field structure |
| `[ValuativeRel K]` | instance | Its valuative relation, which determines `ValuativeRel.valuation K` and the valuation ring `𝒪[K]` |
| `[TopologicalSpace K]` | instance | Its topology |
| `[IsNonarchimedeanLocalField K]` | instance | Mathlib's class of nonarchimedean local fields |
| `x : 𝒪[K]ˣ` | explicit | A unit of the valuation ring |

`integerUnitsToFieldUnits K : 𝒪[K]ˣ →* Kˣ` is the published inclusion
`Units.map (algebraMap 𝒪[K] K).toMonoidHom` from `Basic.U016.Definitions`
(M128.016). `v K : Additive Kˣ → Int` is the published normalized integer
valuation from `Basic.Definitions` (M128.001): the additive exponent
(`Multiplicative.toAdd`) of the nonzero part (`WithZero.unzero`) of the field
valuation of a unit, transported along Mathlib's order isomorphism
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K` onto
`ℤᵐ⁰ = WithZero (Multiplicative Int)`. The statement says that a unit of the
valuation ring has normalized valuation zero as a field unit. No hypothesis
is added.

The sole direct import is the published
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.ValuationStatements`
module. It imports the published `Basic.Definitions` and
`Basic.U016.Definitions` modules, which supply `v` and
`integerUnitsToFieldUnits`. The source proof rewrites with the theorem
`v_apply` (M128.002). No proof of it is in the Library at this workspace's
base, so no proof module is imported; the needed instance is proved
locally, as described below.

## Implemented proof

```lean
intro K _ _ _ _ x
have hxv :
    ValuativeRel.valuation K ((integerUnitsToFieldUnits K x : Kˣ) : K) = 1 := by
  simpa [integerUnitsToFieldUnits] using
    (Valuation.Integers.valuation_unit
      (Valuation.integer.integers (ValuativeRel.valuation K)) x)
-- The source theorem `v_apply K` (M128.002) at this unit, proved by its original `rfl`.
have happly :
    v K (Additive.ofMul (integerUnitsToFieldUnits K x)) =
      Multiplicative.toAdd
        (WithZero.unzero
          (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
            (ValuativeRel.valuation K
              ((Additive.toMul (Additive.ofMul (integerUnitsToFieldUnits K x)) : Kˣ) : K)))
          ((map_ne_zero (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).2
            ((Valuation.ne_zero_iff (ValuativeRel.valuation K)).2
              (Additive.toMul (Additive.ofMul (integerUnitsToFieldUnits K x))).ne_zero))) :=
  rfl
rw [happly]
apply (WithZero.toAdd_unzero_eq_iff _ 0).2
change
  (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
      (ValuativeRel.valuation K
        ((integerUnitsToFieldUnits K x : Kˣ) : K)) =
    ((Multiplicative.ofAdd (0 : Int) : Multiplicative Int) :
      WithZero (Multiplicative Int))
rw [hxv, map_one]
rfl
```

1. `intro K _ _ _ _ x` introduces the six binders of the statement.
2. `hxv`: the image of `x` in `K` has valuation one. Under
   `open scoped ValuativeRel`, the valuation ring `𝒪[K]` is notation for
   `Valuation.integer (ValuativeRel.valuation K)`
   (`Mathlib/Topology/Algebra/Valued/ValuativeRel.lean`, line 88), the ring
   of integers of the valuation. It satisfies `Valuation.Integers` by
   `Valuation.integer.integers`
   (`Mathlib/RingTheory/Valuation/Integers.lean`, line 61).
   `Valuation.Integers.valuation_unit` (same file, line 168) then says that
   a unit of the ring of integers has valuation one. A development `simpa?`
   check reports that `simpa` uses exactly `integerUnitsToFieldUnits`,
   `RingHom.toMonoidHom_eq_coe`, `Units.coe_map` and `MonoidHom.coe_coe` to
   identify the underlying element of `integerUnitsToFieldUnits K x` with
   `algebraMap 𝒪[K] K x`.
3. `happly` is the source theorem `v_apply K` at
   `Additive.ofMul (integerUnitsToFieldUnits K x)`: its statement is that
   instance of the published `v_applyStatement` equation, and it is proved,
   as `v_apply` is in the source, by `rfl`, since the right side is the body
   of the definition of `v`. `rw [happly]` then plays the role of the
   source's `rw [v_apply]`.
4. `WithZero.toAdd_unzero_eq_iff`
   (`Mathlib/Algebra/Order/GroupWithZero/Canonical.lean`, line 375) says
   that the additive exponent of the nonzero part of `a` equals `b` if and
   only if `a = ofAdd b`. Applying its reverse direction with `b = 0`
   reduces the goal to an equation in `ℤᵐ⁰`.
5. `change` restates that equation with `Additive.toMul (Additive.ofMul _)`
   reduced away: the transported valuation of `integerUnitsToFieldUnits K x`
   equals the coercion of `ofAdd 0`.
6. `rw [hxv, map_one]` rewrites the valuation to `1` and its image under
   the order isomorphism to `1`. The remaining goal
   `1 = ((ofAdd 0 : Multiplicative Int) : ℤᵐ⁰)` holds by `rfl`, since
   `ofAdd 0` is the identity of `Multiplicative Int` and the coercion of the
   identity is the identity of `WithZero`.

The development check reports that the theorem has the single level
parameter `u` and compiled with no diagnostics.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`,
lines 206 to the end of file](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean#L206-L228):
the theorem signature at 206–208 and the proof at 209–223; lines 224–228
close the `IsNonarchimedeanLocalField` namespace, the
`noncomputable section` and the `LocalFieldTheory` namespace. The docstring
of `v_integerUnitsToFieldUnits` is at line 204 and its `@[simp]` attribute
at line 205, just before the partition's start line. The source theorem
`v_apply`, whose `rfl` proof is reused for `happly`, is at lines 42–51 of the
same file. The `open scoped ValuativeRel WithZero` directive at line 23 is
kept here. The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`;
it was read and its SHA-256 verified as
`c696d08952343a0f668340bac35e2485e74b52134b0e205a3a4dc0653f48d25e`,
the hash recorded in the partition.

| Original declaration | Adapted declaration in `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField` |
| --- | --- |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v_integerUnitsToFieldUnits` (theorem) | `v_integerUnitsToFieldUnits` (theorem), proving the published target |
| Same theorem's statement | Existing `v_integerUnitsToFieldUnitsStatement` |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v_apply K` at this unit | Local fact `happly` inside the proof; no declaration |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v`, `integerUnitsToFieldUnits` | Existing `v`, `integerUnitsToFieldUnits` |

Only the first row introduces a declaration here. Modifications by
Worker 120 on 13 November 2026 are:

- add the `Langlands.NYLL` namespace prefix and replace the source import
  `Mathlib.NumberTheory.LocalField.Basic` with the sole ValuationStatements
  import, which provides it transitively;
- give the theorem the published closed statement as its type and introduce
  its six binders with `intro K _ _ _ _ x`;
- replace the source's `rw [v_apply]` by `rw [happly]`, where `happly` is
  the needed instance of `v_apply`, proved by the source's `rfl`, because no
  proof of M128.002 is in the Library. No second declaration named
  `v_apply` is published by this module;
- omit the `@[simp]` attribute. The theorem's type is the statement
  constant, not a syntactic equation, so it would not give the source simp
  lemma;
- omit the source `noncomputable section`, which a theorem does not need, and
  all other source declarations.

The theorem name, docstring, the proof of `hxv` and every step after the
rewrite are kept verbatim. The partition records no patch10 change to this
original module.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
Additional attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No NYLL or local-field valuation erratum was found in the Library errata
notes. Searches of staging and shared drafts for
`v_integerUnitsToFieldUnits` found no earlier proof port of this theorem.

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

This module proves only M128.019. It does not publish M128.002 as a
declaration, nor any other M128 theorem.
