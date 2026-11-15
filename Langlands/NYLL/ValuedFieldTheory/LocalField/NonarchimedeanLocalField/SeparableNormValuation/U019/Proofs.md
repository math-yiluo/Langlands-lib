# Normalized valuation of a separable field norm: proof

This module proves the theorem
`Langlands.NYLL.LocalClassFieldTheory.v_normUnits_eq_residue_finrank_mul_of_isSeparable`.
Its type is the published proposition
`Langlands.NYLL.LocalClassFieldTheory.v_normUnits_eq_residue_finrank_mul_of_isSeparableStatement K L x`,
applied to the theorem's own parameters. This is the proof phase of source
unit M162.019 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m145-m168.md#m162).

Mathematically: let `L / K` be a finite separable extension of nonarchimedean
local fields, with the valuation of `L` extending that of `K` and `𝒪[L]` the
integral closure of `𝒪[K]` in `L`. Then for every unit `x` of `L`,
`v_K(N_{L/K}(x)) = f · v_L(x)`, where `f = [𝓀[L] : 𝓀[K]]` is the residue
degree and `v_K`, `v_L` are NYLL's normalized valuations described next.

## Sign convention

NYLL's normalized valuation `v` (M128.001,
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v`) transports
the value of a unit to `ℤₘ₀` through Mathlib's
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt` and takes the integer
exponent. Under this isomorphism a prime element has value
`Multiplicative.ofAdd (-1)`, so **`v` is minus the usual order**: the chosen
prime element `integerRingUniformizerFieldUnit L` has `v = -1` (the M133.018
target `v_integerRingUniformizerFieldUnitStatement`), and its inverse
`inverseIntegerRingUniformizerFieldUnit L` has `v = 1`.

The unit `ϖ` of this proof is that inverse,
`ϖ = inverseIntegerRingUniformizerFieldUnit L = (integerRingUniformizerFieldUnit L)⁻¹`.
It satisfies `v_L(ϖ) = 1` in NYLL's sign convention and is the **inverse of a
uniformizer, not a uniformizer**; the source docstrings call it the "positive
generator". The theorem itself does not depend on the sign: negating `v` on
both fields negates both sides of the equation.

## Target and binders

The theorem's complete telescope and conclusion are

```lean
open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

attribute [local instance] FractionRing.liftAlgebra

theorem v_normUnits_eq_residue_finrank_mul_of_isSeparable
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (x : Lˣ) :
    v_normUnits_eq_residue_finrank_mul_of_isSeparableStatement K L x
```

The binders before the colon are the published statement's parameters in the
same order, with the same binder kinds and names: `K`, `L`, the thirteen
instance binders and `x`. The statement unfolds to

```lean
v K (Additive.ofMul (normUnits K L x)) =
  (Module.finrank 𝓀[K] 𝓀[L] : Int) * v L (Additive.ofMul x)
```

## Imports and dependencies

The direct imports are Library modules (all under
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField`):

| Module | Used declaration (in `Langlands.NYLL.`) | Source unit |
| --- | --- | --- |
| `SeparableNormValuation.U019.Statements` | `LocalClassFieldTheory.v_normUnits_eq_residue_finrank_mul_of_isSeparableStatement` (the target) | M162.019 (statement) |
| `SeparableNormValuation.U018.Proofs` | `LocalClassFieldTheory.v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparable` | M162.018 |
| `ValuationExactSequence.U028.Proofs` | `LocalFieldTheory.IsNonarchimedeanLocalField.uniformizerUnitFactor_mul_uniformizer_zpow`; its import provides `uniformizerUnitFactor` (M134.038) | M134.040 |
| `IdealQuotients.U005.Proofs` | `LocalFieldTheory.chosenIntegerRingUniformizer_irreducible`; its imports provide `chosenIntegerRingUniformizer` (M133.004) | M133.005 |
| `IdealQuotients.U007.Definitions` | `LocalFieldTheory.integerRingUniformizerFieldUnit`, `LocalFieldTheory.inverseIntegerRingUniformizerFieldUnit` | M133.007, M133.009 |
| `IdealQuotients.U016.Proofs` | `LocalFieldTheory.v_integerRingIrreducibleFieldUnit_inv` | M133.016 |
| `Basic.U004.Proofs` | `LocalFieldTheory.IsNonarchimedeanLocalField.v_mul` | M128.004 |
| `Basic.U009.Proofs` | `LocalFieldTheory.IsNonarchimedeanLocalField.v_zpow` | M128.009 |
| `Basic.U019.Proofs` | `LocalFieldTheory.IsNonarchimedeanLocalField.v_integerUnitsToFieldUnits`; its import provides `integerUnitsToFieldUnits` (M128.016) | M128.019 |
| `Norm.U019.Definitions` | `LocalFieldTheory.IsNonarchimedeanLocalField.normIntegerUnits` | M129.022 |

The definitions `v` (M128.001) and `normUnits` (M092.002,
`Units.map (Algebra.norm K)`) reach this module through the Statements import.
`normIntegerUnits K L` needs the instance `LocalFieldTheory.ValuativeExtension K L`;
it is found from the hypothesis `[IsIntegralClosure 𝒪[L] 𝒪[K] L]` by the
published instance `valuativeExtensionOfIsIntegralClosure`.

The imported `uniformizerUnitFactor` and
`uniformizerUnitFactor_mul_uniformizer_zpow` are phrased with the bundled
normalized valuation `valuationMap` (M134.002), while this proof uses `v`.
The two agree definitionally on every unit (`valuationMap` bundles the same
exponent of the same `ℤₘ₀`-value), so the facts stated with `v` below are
accepted where `valuationMap` is expected, as in the source proof.

The source theorem `v_inverseIntegerRingUniformizerFieldUnit` (M133.019) is
not imported: its statement target
`v_inverseIntegerRingUniformizerFieldUnitStatement` is published, but its
proof is not in the Library at this module's base commit. The needed instance
at `L` is proved locally (step 1 below); no declaration of that name is
introduced.

The Mathlib results used are `map_mul` and `map_zpow`
(`Mathlib/Algebra/Group/Hom/Defs.lean`, lines 326 and 495: a monoid
homomorphism preserves products, and a monoid homomorphism from a group
preserves integer powers), `Units.ext` (`Mathlib/Algebra/Group/Units/Defs.lean`,
line 119: units with equal values are equal), `zero_add`, and the `ring`
tactic.

## Implemented proof

The proof begins with `unfold` of the statement constant, exposing the
equation above. Then:

1. **Local M133.019 fact `hinvPrime`.**
   `v L (Additive.ofMul (inverseIntegerRingUniformizerFieldUnit L)) = 1`,
   that is, the inverse of the chosen prime element has value `1` in NYLL's
   sign convention (the prime element itself has value `-1`). It is proved by
   the two-line source proof of M133.019 (`IdealQuotients.lean`, lines
   277–285): `rw [inverseIntegerRingUniformizerFieldUnit]` turns the unit into
   `(integerRingUniformizerFieldUnit L)⁻¹`, and
   `v_integerRingIrreducibleFieldUnit_inv L (chosenIntegerRingUniformizer L)
   (chosenIntegerRingUniformizer_irreducible L) (integerRingUniformizerFieldUnit L) rfl`
   (M133.016) gives exactly that equation; the `rfl` proves that the field
   unit's value is the chosen prime element, which holds by the definition
   `Units.mk0` of `integerRingUniformizerFieldUnit`.
2. **Setup.** `ϖ := inverseIntegerRingUniformizerFieldUnit L`, the inverse of
   a uniformizer with `hϖ : v L (Additive.ofMul ϖ) = 1` (from `hinvPrime`);
   `n := v L (Additive.ofMul x)`; and the valuation-ring unit
   `a := uniformizerUnitFactor L ϖ hϖ x : 𝒪[L]ˣ`.
3. **`haNorm`.** `normUnits K L (integerUnitsToFieldUnits L a) =
   integerUnitsToFieldUnits K (normIntegerUnits K L a)`, by `Units.ext` and
   `rfl`: both units have value `Algebra.norm K (a : L)`.
4. **`hx`.** `integerUnitsToFieldUnits L a * ϖ ^ n = x`, which is
   `uniformizerUnitFactor_mul_uniformizer_zpow L ϖ hϖ x` (M134.040). Since
   `v L ϖ = 1` in NYLL's sign convention, this is the decomposition
   `x = a · ϖ^{v_L(x)}` with `ϖ` the inverse of a uniformizer.
5. **`hxNorm`.** Applying `normUnits K L` to `hx` and using `map_mul`,
   `map_zpow` and `haNorm` gives
   `normUnits K L x = integerUnitsToFieldUnits K (normIntegerUnits K L a) *
   (normUnits K L ϖ) ^ n` (a three-step `calc`).
6. **Conclusion.** `rw [hxNorm, v_mul, v_integerUnitsToFieldUnits, zero_add,
   v_zpow, v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparable]`
   rewrites the left side to `n * f`: `v_mul` (M128.004) splits the product,
   `v_integerUnitsToFieldUnits` (M128.019) gives the integral unit value `0`,
   `v_zpow` (M128.009) gives `n * v K (Additive.ofMul (normUnits K L ϖ))`,
   and M162.018 gives `v K (Additive.ofMul (normUnits K L ϖ)) = f` for
   `f = (Module.finrank 𝓀[K] 𝓀[L] : Int)`. Finally `simp only [n]` unfolds
   the local definition `n` and `ring` closes
   `v L (Additive.ofMul x) * f = f * v L (Additive.ofMul x)`.

The imported `v_mul`, `v_zpow`, `v_integerUnitsToFieldUnits` and
`uniformizerUnitFactor_mul_uniformizer_zpow` prove closed statement constants
(universally quantified `...Statement.{u}`) and are applied to explicit
arguments or used by `rw`, which unfolds those constants.

The module has no auxiliary declarations. The local instance attribute on
`FractionRing.liftAlgebra` is scoped to this module and kept from the source
file (line 321), as in the statement file and the M162.018 proof module, but
this proof does not use it: a development probe of the same module with the
attribute line deleted also compiled with no errors and no warnings.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean),
SHA-256 `b54bcd01a217ffc5fb905d410fe9ef64ebf87e5d7192509332cad827fc22c90e`.
The relevant lines are the file-level local instance attribute at line 321
and the theorem at lines 492–537 (docstring 492–494, statement 495–508, proof
509–537). The locally reproduced M133.019 proof is from
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/IdealQuotients.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/IdealQuotients.lean),
SHA-256 `8c7082cb0e2e8ac6db22ff1afd4a1d173032246eac681ed075bb9feab7c5f71e`,
theorem `v_inverseIntegerRingUniformizerFieldUnit` at lines 277–285
(docstring 274–276).

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.v_normUnits_eq_residue_finrank_mul_of_isSeparable` (M162.019) | `Langlands.NYLL.LocalClassFieldTheory.v_normUnits_eq_residue_finrank_mul_of_isSeparable`, proving the published target |
| Same theorem's statement | Existing `v_normUnits_eq_residue_finrank_mul_of_isSeparableStatement` |
| `LocalFieldTheory.v_inverseIntegerRingUniformizerFieldUnit` (M133.019), used | Local fact `hinvPrime` at `L`, proved by the source proof; no declaration |
| `LocalClassFieldTheory.v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparable` (M162.018), used | Imported under the same name with the `Langlands.NYLL.` prefix |
| `uniformizerUnitFactor` (M134.038), `uniformizerUnitFactor_mul_uniformizer_zpow` (M134.040), `normIntegerUnits` (M129.022), `integerUnitsToFieldUnits` (M128.016), `v_mul` (M128.004), `v_zpow` (M128.009), `v_integerUnitsToFieldUnits` (M128.019), used | Imported under the same names in `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField` |
| `inverseIntegerRingUniformizerFieldUnit` (M133.009), `integerRingUniformizerFieldUnit` (M133.007), `chosenIntegerRingUniformizer` (M133.004), `chosenIntegerRingUniformizer_irreducible` (M133.005), `v_integerRingIrreducibleFieldUnit_inv` (M133.016), used | Imported under the same names in `Langlands.NYLL.LocalFieldTheory` |

Modifications by Worker 369 on 15 November 2026:

- the namespace gets the `Langlands.NYLL` prefix, and the source imports are
  replaced by the modules listed above;
- the theorem's type is the statement constant
  `v_normUnits_eq_residue_finrank_mul_of_isSeparableStatement K L x` instead
  of the equation it unfolds to, and the proof begins with `unfold` of that
  constant;
- the source's `hϖ := v_inverseIntegerRingUniformizerFieldUnit L` is replaced
  by the local fact `hinvPrime`, proved before `ϖ` is introduced by the
  M133.019 source proof specialized to `L`; `hϖ` is then `hinvPrime`;
- the remaining source lines 512–537 (`n`, `a`, `haNorm`, `hx`, `hxNorm` and
  the final `rw`, `simp only [n]`, `ring`) are unchanged;
- every other declaration of the source files is omitted.

The theorem name, docstring, binders and the local instance attribute are
kept.

The retained originals belong to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`; the attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. Searches
of the workspace, the current Library, staging and shared drafts found no
earlier proof of this target. Worker 85's task context recorded a private
replay of the same route against this target; this module was written and
checked independently from the pinned original.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean
4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. A development
check built the module with no errors and no warnings and found a theorem with
level parameters `u`, `v` using only the axioms `propext`, `Classical.choice`
and `Quot.sound`. This check is not independent semantic acceptance or
Integrator publication.

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright
2026 Naganori Yamaguchi, author “Naganori Yamaguchi (assisted by OpenAI
Codex)”, released under Apache-2.0. The Lean file carries Worker 369's dated
modification record. Worker 369 adapted this proof directly from the pinned
original and wrote this companion. Worker 85's statement is used unchanged;
the imported statement and proof modules and their paired Markdown remain
frozen.

The unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are reused, with SHA-256
hashes `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. No
Mathlib code is copied into this file.

This module proves only M162.019. It does not prove or publish M133.019
(`v_inverseIntegerRingUniformizerFieldUnit`), whose proof is routed
separately.
