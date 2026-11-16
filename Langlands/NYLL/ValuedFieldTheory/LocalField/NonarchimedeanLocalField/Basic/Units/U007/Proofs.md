# The normalized valuation of a quotient

This module proves the theorem
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_div`, the proof phase of
M128.007 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m128).
Its type is the published proposition
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_divStatement` applied to the
theorem's parameters:

```lean
theorem v_div (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x y : Kˣ) :
    v_divStatement K x y
```

## Target and binders

The theorem takes `K` with its instances `[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]`, `x` and `y`, exactly as the published target and the source theorem; the module declares no section variables.

By its definition in the published module `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.Units.Statements`, the target is the proposition

```lean
v K (Additive.ofMul (x / y)) =
  v K (Additive.ofMul x) - v K (Additive.ofMul y)
```

Here `K` is a nonarchimedean local field (Mathlib's `IsNonarchimedeanLocalField K`, with `ValuativeRel K` and `TopologicalSpace K`), `x y : Kˣ`, and `v K : Additive Kˣ → Int` (M128.001) is the normalized integer valuation: the exponent of the value of a unit after transporting the value group to `WithZero (Multiplicative Int)`. The target says `v(x / y) = v(x) - v(y)`. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.Units.Statements`, which defines the target and imports `v` (M128.001);
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U004.Proofs`, the published proof of M128.004 `v_mul`, of type `v_mulStatement`, which unfolds to `∀ K [...] (x y : Kˣ), v K (Additive.ofMul (x * y)) = v K (Additive.ofMul x) + v K (Additive.ofMul y)`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U006.Proofs`, the published proof of M128.006 `v_inv`, of type `v_invStatement`, which unfolds to `∀ K [...] (x : Kˣ), v K (Additive.ofMul x⁻¹) = -v K (Additive.ofMul x)`.

The module opens `ValuativeRel` and `WithZero` scoped, as the source and the published statement module do; the proof uses none of their notation.

## Implemented proof

After `show` states the published proposition unfolded, the proof states the published `v_mul K` and `v_inv K` as the local facts `hmul` and `hinv` (their `...Statement` types are accepted by definitional unfolding, but `rw` needs the unfolded equations). The rest is the source proof with `hmul` and `hinv` in place of `v_mul` and `v_inv`: `rw [div_eq_mul_inv, hmul, hinv, sub_eq_add_neg]` turns the goal `v(x * y⁻¹) = v(x) - v(y)` into `v(x) + -v(y) = v(x) + -v(y)`, which `rw` closes by reflexivity.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`, lines 105–110](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean#L105-L110):
the docstring at line 105 and the theorem at lines 106–110. It lies in `namespace LocalFieldTheory` (line 15), its `noncomputable section` (line 17), `universe u` (line 19), `namespace IsNonarchimedeanLocalField` (line 21) and `open scoped ValuativeRel WithZero` (line 23). The source is:

```lean
/-- The normalized valuation of a quotient is the difference of the two valuations. -/
theorem v_div (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x y : Kˣ) :
    v K (Additive.ofMul (x / y)) =
      v K (Additive.ofMul x) - v K (Additive.ofMul y) := by
  rw [div_eq_mul_inv, v_mul, v_inv, sub_eq_add_neg]
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`;
its SHA-256 is `c696d08952343a0f668340bac35e2485e74b52134b0e205a3a4dc0653f48d25e`.

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- give the theorem the published proposition `v_divStatement K x y` as its type, and begin the proof with `show` stating it unfolded;
- state the published `...Statement`-typed M128.004 `v_mul K` and M128.006 `v_inv K` unfolded as the local facts `hmul` and `hinv`, and rewrite with these in place of the source's `v_mul` and `v_inv`;
- omit all other source declarations.

The theorem's name, docstring, binders and the remaining proof steps are the source's. The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; additional
attribution material is registered as `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright 2026
Naganori Yamaguchi, author “Naganori Yamaguchi (assisted by OpenAI Codex)”, released
under Apache-2.0. The Lean file carries the dated modification record. The unchanged
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in the
Library. No Mathlib code is copied.

Worker 5264 wrote this proof and its companion Markdown as the shared draft
for Task 7140; Worker 748 verified and submitted it.

This module proves only M128.007; it discharges no other NYLL target.
