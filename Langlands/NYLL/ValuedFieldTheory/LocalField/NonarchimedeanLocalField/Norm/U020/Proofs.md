# Norm value of a valuation-ring unit times that of its inverse: exact proof

This module proves
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.normIntegerUnitsValue_mul_inv`
with exactly the closed type
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.normIntegerUnitsValue_mul_invStatement.{u, v}`.
Its independent universe parameters are `u` and `v`, in that order. The
published statement module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm.InverseStatements`
is imported unchanged.

The proposition's complete internal telescope is

```lean
∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [ValuativeRel L]
  [Langlands.NYLL.LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]ˣ),
  normIntegerUnitsValue (K := K) (L := L) x *
    normIntegerUnitsValue (K := K) (L := L) x⁻¹ = 1
```

Here `𝒪[K]` is `Valuation.integer (ValuativeRel.valuation K)`, and the
published definition
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.normIntegerUnitsValue`
(module `Norm.U019.Definitions`) sends a unit `x` of `𝒪[L]` to the element
`Algebra.norm K (x : L)` of `𝒪[K]`. The namespaced `ValuativeExtension`
class says that every element of `𝒪[L]` is integral over `𝒪[K]`; it is used
only by that definition's membership proof. The theorem has no
finite-dimensionality or local-field hypothesis; the inherited namespace
introduces no such assumption.

## Implemented proof

After introducing the two fields, the six structure instances and `x`, the
proof is the original source tactic block:

1. `ext` reduces the equation in the subring `𝒪[K]` to the equation of the
   underlying elements of `K`.
2. `change` displays that goal, by definitional unfolding of
   `normIntegerUnitsValue` and of the subring multiplication and one, as
   `Algebra.norm K (x : L) * Algebra.norm K (x⁻¹ : L) = 1`.
3. The local fact `hx : (x : L) * (x⁻¹ : L) = 1` is obtained by applying
   the coercion `𝒪[L]ˣ → 𝒪[L] → L` (via `congrArg`) to the unit identity
   `mul_inv_cancel x`.
4. Rewriting backwards with `map_mul (Algebra.norm K)` turns the goal into
   `Algebra.norm K ((x : L) * (x⁻¹ : L)) = 1`; rewriting with `hx` and then
   `map_one` closes it.

The membership proof stored in `normIntegerUnitsValue` plays no role, since
only underlying elements are compared.

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
Lines 1–35, 60–68 and 170–210 were read. Lines 20–30 supply the
namespaces, universes, scoped openings and field variables, line 65 the
field and algebra instances, and lines 179–191 the statement and proof of
M129.020 (the next unit, M129.021, starts at line 192).

The source lemma
`LocalFieldTheory.IsNonarchimedeanLocalField.normIntegerUnitsValue_mul_inv`
becomes the identically suffixed theorem in the `Langlands.NYLL` namespace.
This is the proof phase of M129.020 in
`notes/reuse/nyll-public-port/m121-m144.md`. The tactic block is copied
unchanged; only the closed target's telescope is introduced first.

Worker 135 made these changes on 14 November 2026:

- Prefix the namespace with `Langlands.NYLL`.
- State the theorem with the published closed proposition as its entire type,
  preserving universes `.{u, v}` and the internal binder order and kinds, and
  introduce that telescope with `intro`.
- Use the keyword `theorem` instead of the source `lemma`.
- Omit all other declarations of the original file, its
  `noncomputable section` and its section variables.
- Replace the original imports by the single import below.
- Retain the original copyright, license and author header and add the
  modification comment and this paired explanation.

## Actual imports

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm.InverseStatements`
  supplies the exact published target and, through its import
  `Norm.U019.Definitions`, the definition `normIntegerUnitsValue`, the
  namespaced `ValuativeExtension` class, the valuation-ring notation and the
  Mathlib field norm with `map_mul` and `map_one`.

No other NYLL proof is used. The published monoid hom `normIntegerUnits`
in the same definitions module contains the same computation in its
`val_inv` field, but this proof does not use it.

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
