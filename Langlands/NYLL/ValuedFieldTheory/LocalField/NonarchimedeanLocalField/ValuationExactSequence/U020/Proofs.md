# Field units of additive valuation zero: exact proof

This module proves
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuation_eq_one_of_valuationMap_eq_zero`
with exactly the closed type
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuation_eq_one_of_valuationMap_eq_zeroStatement.{u}`.
Its universe parameter is `u`. The published statement module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.KernelStatements`
is imported unchanged.

The proposition's complete internal telescope is

```lean
∀ (K : Type u)
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {x : Kˣ} (hx : valuationMap K (Additive.ofMul x) = 0),
  ValuativeRel.valuation K (x : K) = 1
```

`IsNonarchimedeanLocalField` is Mathlib's root class. The published
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K :
Additive Kˣ →+ Int` (module `ValuationExactSequence.Definitions`) is the
normalized additive valuation on field units, built from Mathlib's order
isomorphism
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K :
ValueGroupWithZero K ≃*o ℤᵐ⁰`. The theorem says that a unit of additive
valuation `0` has multiplicative valuation `1`.

## Implemented proof

After introducing `K`, its four structure instances, `x` and `hx`, the proof
is the original source tactic block. Write `e` for
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K` and `z` for
`WithZero.unzero` applied to `e (ValuativeRel.valuation K (x : K))` with the
nonvanishing proof built from `map_ne_zero e`, `Valuation.ne_zero_iff` and
`x.ne_zero`.

1. `rw [valuationMap_apply] at hx` uses the published M134.004 theorem
   `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_apply`
   to rewrite `hx` as `v K (Additive.ofMul x) = 0`, where `v` is the published
   M128 definition
   `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v`.
2. `dsimp [v] at hx` unfolds `v`, so `hx` says that `Multiplicative.toAdd z`
   is `0`.
3. The local fact `hunzero : z = 1` in `Multiplicative Int` follows by
   applying `Multiplicative.ofAdd` to `hx` and simplifying.
4. `apply e.injective` reduces the goal to
   `e (ValuativeRel.valuation K (x : K)) = e 1`.
5. The local fact `hcoe` is `hunzero` pushed into `ℤᵐ⁰` along the
   coercion `Multiplicative Int → WithZero (Multiplicative Int)`.
   `rw [WithZero.coe_unzero] at hcoe` turns it into
   `e (ValuativeRel.valuation K (x : K)) = 1`.
6. `simpa using hcoe` closes the goal, `map_one` identifying `e 1` with `1`.

## Source and correspondence

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean`,
SHA-256 `8a8515596e4388771957f2c4c484e8c86767236ab79f973fa405df2d34e02908`.
It is available in registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement
is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Lines 1–80 and 170–210 were read. Lines 20–28 supply the namespaces,
universe and scoped openings, lines 48–54 the M134.004 lemma
`valuationMap_apply`, and lines 178–207 the statement and proof of M134.020
(the next unit, M134.021, starts at line 208).

The source theorem
`LocalFieldTheory.IsNonarchimedeanLocalField.valuation_eq_one_of_valuationMap_eq_zero`
becomes the identically suffixed theorem in the `Langlands.NYLL` namespace.
This is the proof phase of M134.020 in
`notes/reuse/nyll-public-port/m121-m144.md`. The tactic block is copied
unchanged; only the closed target's telescope is introduced first. Its one
prerequisite, M134.004 `valuationMap_apply`, is the already published
theorem of the same adapted name, imported here; it is not re-proved.

Worker 135 made these changes on 14 November 2026:

- Prefix the namespace with `Langlands.NYLL`.
- State the theorem with the published closed proposition as its entire type,
  preserving universe `.{u}` and the binder order and kinds, and introduce
  that telescope with `intro`.
- Omit all other declarations of the original file, its
  `noncomputable section` and its `universe` declaration.
- Replace the original imports by the two imports below.
- Retain the original copyright, license and author header and add the
  modification comment and this paired explanation.

## Actual imports

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.KernelStatements`
  supplies the exact published target. Through its import
  `ValuationExactSequence.Definitions` it also supplies `valuationMap`, and
  through that module's import `Mathlib.NumberTheory.LocalField.Basic` it
  supplies Mathlib's `valueGroupWithZeroIsoInt`. Its other import,
  `Basic.U016.Definitions`, also imports only that Mathlib module. Neither
  import declares the NYLL definition `v`.
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U004.Proofs`
  supplies the published theorem `valuationMap_apply` (M134.004). It also
  supplies the definition `v` used in steps 1 and 2: `U004.Proofs` imports
  `ValuationExactSequence.EvaluationStatements`, which imports
  `NonarchimedeanLocalField.Basic.Definitions`, where `v` is declared.

The original imports, NYLL `NonarchimedeanLocalField.Valuation` and
`IdealQuotients`, `Mathlib.Algebra.Group.Hom.Basic` and
`Mathlib.RingTheory.Valuation.Discrete.Basic`, are unnecessary for this
proof.

## Development check

In environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), the module compiled
with no errors or warnings. Declaration inspection reports a theorem with
level parameters `[u]` and only `propext`, `Classical.choice` and
`Quot.sound`. This development check is separate from candidate
exact-target validation and independent semantic review.

## Attribution

The retained original header credits Naganori Yamaguchi (assisted by OpenAI
Codex) and releases the source under Apache-2.0. The unchanged upstream
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are already published.
Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No other worker's unpublished draft was reused.
