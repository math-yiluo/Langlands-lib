# Surjectivity of the bundled valuation map

This module proves the theorem
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_surjective`.
Its type is the already published proposition
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_surjectiveStatement`
at the universe level `u`:

```lean
theorem valuationMap_surjective : valuationMap_surjectiveStatement.{u}
```

This is the proof phase of M134.005 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m134).

## Target and binders

By its definition in the published `ValuationExactSequence.EvaluationStatements`
module, `valuationMap_surjectiveStatement.{u}` is the closed proposition

```lean
∀ (K : Type u) [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K],
  Function.Surjective (valuationMap K)
```

The binders are exactly the source theorem's, in source order:

| Binder | Kind | Meaning |
| --- | --- | --- |
| `K : Type u` | explicit | The field |
| `[Field K]` | instance | Its field structure |
| `[ValuativeRel K]` | instance | Its valuative relation, which determines `ValuativeRel.valuation K` |
| `[TopologicalSpace K]` | instance | Its topology |
| `[IsNonarchimedeanLocalField K]` | instance | Mathlib's class of nonarchimedean local fields |

`valuationMap K : Additive Kˣ →+ Int` is the published additive homomorphism
from `ValuationExactSequence.Definitions` (M134.002), the additive form
`MonoidHom.toAdditive (valuationUnitsMulHom K)` of the multiplicative
normalized valuation `valuationUnitsMulHom K : Kˣ →* Multiplicative Int`
(M134.001). The latter composes `Units.map` of the field valuation, `Units.map`
of Mathlib's order isomorphism
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K` onto
`ℤᵐ⁰ = WithZero (Multiplicative Int)`, and `WithZero.unitsWithZeroEquiv`.
The statement says that every integer is the value of `valuationMap K` on
some field unit. No hypothesis is added.

The sole direct import is the published
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.EvaluationStatements`
module. It imports the published `ValuationExactSequence.Definitions` module,
which supplies `valuationMap`, and the published `Basic.Definitions` module,
which supplies the normalized integer valuation `v` (M128.001). No other
proof module is imported.

## Implemented proof

```lean
intro K _ _ _ _
-- The source proof of `v_surjective K` (M128.003), inlined.
have hv : Function.Surjective (v K) := by
  intro n
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
exact hv
```

1. `intro K _ _ _ _` introduces the five binders of the statement.
2. The local fact `hv : Function.Surjective (v K)` is the source theorem
   `v_surjective K` (M128.003). No proof of M128.003 is in the Library at
   this workspace's base, so the fact is proved here by the source proof of
   `v_surjective`, copied verbatim. In outline: for an integer `n`, `γ` is
   the element of the value group with zero corresponding to `ofAdd n`;
   `ValuativeRel.valuation_surjective`
   (`Mathlib/RingTheory/Valuation/ValuativeRel/Basic.lean`, line 993) gives
   `a : K` with valuation `γ`; `γ` is nonzero because the inverse
   isomorphism preserves nonzero elements and `ofAdd n` is a nonzero element
   of `WithZero`, so `a` is nonzero; and the unit `Units.mk0 a ha0` has
   normalized valuation `n`, which `simp` computes by unfolding `v` and `γ`,
   rewriting with `ha` and cancelling the isomorphism with its inverse.
3. `exact hv` closes `Function.Surjective (valuationMap K)` with
   `Function.Surjective (v K)`. Lean accepts this because, for every
   `x : Additive Kˣ`, `valuationMap K x` and `v K x` are definitionally
   equal: both reduce to `Multiplicative.toAdd` of the nonzero part of the
   transported valuation of `x`. This is the same definitional equality that
   the source theorem `valuationMap_apply` (M134.004) proves by `rfl`, and it
   is how the source term `v_surjective K` is accepted at this type.

The development check reports that the theorem has the single level
parameter `u` and uses only `propext`, `Classical.choice` and `Quot.sound`,
all already used by the imported definitions and Mathlib; the proof adds no
further axiom.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean`,
lines 57–62](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean#L57-L62):
the theorem signature at 57–59, the proof term `v_surjective K` at 60 and a
blank line at 61; line 62 is the docstring of the next theorem. The docstring
of `valuationMap_surjective` is at line 56, just before the partition's start
line. The inlined prerequisite is the proof of `v_surjective`,
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`,
lines 57–70](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean#L57-L70).
Both passages lie in the `LocalFieldTheory` namespace and its
`noncomputable section`, in the inner `IsNonarchimedeanLocalField` namespace
whose `open scoped ValuativeRel WithZero` directive is kept here. The
complete original files are retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/`;
they were read and their SHA-256 hashes verified as
`8a8515596e4388771957f2c4c484e8c86767236ab79f973fa405df2d34e02908`
(`ValuationExactSequence.lean`) and
`c696d08952343a0f668340bac35e2485e74b52134b0e205a3a4dc0653f48d25e`
(`Basic.lean`), the hashes recorded in the partition.

| Original declaration | Adapted declaration in `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField` |
| --- | --- |
| `LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_surjective` (theorem) | `valuationMap_surjective` (theorem), proving the published target |
| Same theorem's statement | Existing `valuationMap_surjectiveStatement` |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v_surjective K` | Local fact `hv` inside the proof; no declaration |
| `LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap`, `v` | Existing `valuationMap`, `v` |

Only the first row introduces a declaration here. Modifications by
Worker 120 on 13 November 2026 are:

- add the `Langlands.NYLL` namespace prefix and replace the source imports
  with the sole EvaluationStatements import;
- give the theorem the published closed statement as its type and introduce
  its binders with `intro K _ _ _ _`;
- replace the source term `v_surjective K` by the local fact `hv`, proved by
  the verbatim source proof of `v_surjective`, because no proof of M128.003
  is in the Library. No second declaration named `v_surjective` is
  published by this module;
- omit the source `noncomputable section`, which a theorem does not need, and
  all other source declarations.

The theorem name and docstring are kept. The partition records no patch10
change to either original module.

The retained originals belong to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
Additional attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No NYLL or local-field valuation erratum was found in the Library errata
notes. Searches of staging and shared drafts for `valuationMap_surjective`
found no earlier proof port of this theorem.

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

This module proves only M134.005. It does not publish M128.003 as a
declaration, nor any other M134 theorem.
