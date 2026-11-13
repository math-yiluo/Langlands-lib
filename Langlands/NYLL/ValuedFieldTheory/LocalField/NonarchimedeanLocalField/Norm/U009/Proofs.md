# Norms of valuation integers: exact proof

This module proves
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.algebraNorm_mem_integers_of_mem_integers`
with exactly the closed type
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.algebraNorm_mem_integers_of_mem_integersStatement.{u, v}`.
Its independent universe parameters are `u` and `v`, in that order. The
published statement is imported unchanged.

The proposition's complete internal telescope is

```lean
∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L]
  [Langlands.NYLL.LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]),
  Algebra.norm K (x : L) ∈ 𝒪[K]
```

Here `𝒪[K]` denotes `Valuation.integer (ValuativeRel.valuation K)`.
The namespaced `ValuativeExtension` class says that every `x : 𝒪[L]`,
viewed in `L`, is integral over `𝒪[K]`. This is the class imported by the
published target. Mathlib's root class with the same short name instead
compares valuative relations; it is not a hypothesis of this theorem.

## Implemented proof

After introducing the two fields, the six structure instances and `x`, the
proof is the original source term:

1. `LocalFieldTheory.ValuativeExtension.integer_isIntegral x` gives
   `IsIntegral 𝒪[K] (x : L)`.
2. `Algebra.isIntegral_norm K` sends that evidence to integrality of
   `Algebra.norm K (x : L)` over `𝒪[K]`.
3. `Valuation.Integers.mem_of_integral`, applied to
   `Valuation.integer.integers (ValuativeRel.valuation K)`, turns this
   integrality into membership in `𝒪[K]`.

The algebra structures and scalar tower needed internally by the Mathlib
norm lemma are the canonical restrictions of `Algebra K L` to the subring
`𝒪[K]`; they are inferred, with no additional premise. The theorem has no
finite-dimensionality or local-field hypothesis. Mathlib's unrestricted norm
is `1` outside the finite-module case, and `Algebra.isIntegral_norm` already
handles that case. The inherited namespace introduces no local-field
assumption.

## Source and correspondence

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Norm.lean`,
SHA-256 `0e9e3d68b6d964addae89ea2185146fdee7c6b60bf23cfff679a20f34e808eb6`.
It is available in registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement
is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Lines 1–132 were read. Lines 20–30 supply the namespaces, universes and field
variables, lines 63–65 the field and algebra instances, and lines 101–107
the statement and proof of M129.009.

The source declaration
`LocalFieldTheory.IsNonarchimedeanLocalField.algebraNorm_mem_integers_of_mem_integers`
becomes the identically suffixed theorem in the `Langlands.NYLL` namespace.
This is the proof phase of M129.009 in
`notes/reuse/nyll-public-port/m121-m144.md`. Its proof route and final term
are unchanged; only the closed target's telescope is introduced first.

Worker 259 made these changes on 13 November 2026:

- Prefix the namespace with `Langlands.NYLL`.
- State the theorem with the published closed proposition as its entire type,
  preserving universes `.{u, v}` and the internal binder order and kinds.
- Omit all other declarations from the original file.
- Replace the original imports with the three imports below. Omit the unused
  `noncomputable section` and scoped openings.
- Retain the original copyright, license and author header and add the
  modification comment and this paired explanation.

## Actual imports

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm.U009.Statements`
  supplies the exact published target, the namespaced integrality class and
  its valuation-ring notation and instances.
- `Mathlib.RingTheory.Norm.Transitivity` supplies `Algebra.isIntegral_norm`.
- `Mathlib.RingTheory.Valuation.Integral` supplies
  `Valuation.Integers.mem_of_integral`.

The original imports `Mathlib.LinearAlgebra.Determinant`, NYLL `NormUnits`
and NYLL `NonarchimedeanLocalField.Basic` are unnecessary for this proof.
The NYLL `ValuativeExtension` import is obtained through the target.
No preceding theorem of the original `Norm.lean` is needed. The already
published
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.normIntegerUnitsValue`
(module `Norm.U019.Definitions`) contains the same integrality reasoning for
units, but this proof does not import or use it.

## Development check

In environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), the module compiled
with no errors or warnings. Declaration inspection reports a theorem with
level parameters `[u, v]` and only `propext`, `Classical.choice` and
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
