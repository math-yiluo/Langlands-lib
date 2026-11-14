# Normalized valuation of the norm of the inverse chosen prime element: proof

This module proves the theorem
`Langlands.NYLL.LocalClassFieldTheory.v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparable`.
Its type is the published proposition
`Langlands.NYLL.LocalClassFieldTheory.v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparableStatement K L`,
applied to the theorem's own parameters. This is the proof phase of source
unit M162.018 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m145-m168.md#m162).

Mathematically: for a finite separable extension `L / K` of nonarchimedean
local fields, with the valuation of `L` extending that of `K` and `𝒪[L]` the
integral closure of `𝒪[K]` in `L`, the field norm of the inverse `ϖ_L⁻¹` of
the chosen prime element of `L` has NYLL-normalized value
`v_K(N_{L/K}(ϖ_L⁻¹)) = f`, where `f = [𝓀[L] : 𝓀[K]]` is the residue degree.
(NYLL's `v` gives a prime element the value `-1`, so `ϖ_L⁻¹` is the
"positive generator" of the source docstring.)

## Target and binders

The theorem's complete telescope and conclusion are

```lean
open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

attribute [local instance] FractionRing.liftAlgebra

theorem v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparable
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparableStatement K L
```

The binders before the colon are the published statement's parameters in the
same order, with the same binder kinds and names. The statement unfolds to

```lean
v K (Additive.ofMul
    (normUnits K L (inverseIntegerRingUniformizerFieldUnit L))) =
  (Module.finrank 𝓀[K] 𝓀[L] : Int)
```

## Imports and dependencies

The direct imports are Library modules:

| Module (under `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField`) | Used declaration | Source unit |
| --- | --- | --- |
| `SeparableNormValuation.UniformizerNorm.Statements` | the target statement | M162.018 (statement) |
| `SeparableNormValuation.U017.Proofs` | `Langlands.NYLL.LocalClassFieldTheory.v_normUnits_integerRingUniformizerFieldUnit_of_isSeparable` | M162.017 |
| `Basic.U006.Proofs` | `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_inv` | M128.006 |

The definitions `v` (M128.001), `normUnits` (M092.002),
`integerRingUniformizerFieldUnit` (M133.007) and
`inverseIntegerRingUniformizerFieldUnit` (M133.009) reach this module through
the Statements import. The proof unfolds
`inverseIntegerRingUniformizerFieldUnit L`, which is defined as
`(integerRingUniformizerFieldUnit L)⁻¹`, and uses that `normUnits K L` is a
monoid homomorphism `Lˣ →* Kˣ` (it is `Units.map (Algebra.norm K)`).

The Mathlib results used are:

- `map_inv` (`Mathlib/Algebra/Group/Hom/Defs.lean`, line 440): a monoid
  homomorphism between groups preserves inverses, `f a⁻¹ = (f a)⁻¹`;
- `neg_neg`, the additive form of `inv_inv`
  (`Mathlib/Algebra/Group/DivInvMonoid.lean`, line 57): `-(-a) = a`.

## Implemented proof

1. **The inverse rule `hinv`.** The local fact
   `v K (Additive.ofMul (normUnits K L (integerRingUniformizerFieldUnit L))⁻¹)
   = -v K (Additive.ofMul (normUnits K L (integerRingUniformizerFieldUnit L)))`
   is `v_inv K _` (M128.006). The type of `v_inv` is the statement constant
   `v_invStatement`, which Lean unfolds when it checks the ascribed type.
2. **The prime-element value `hprime`.** The local fact
   `v K (Additive.ofMul (normUnits K L (integerRingUniformizerFieldUnit L)))
   = -(Module.finrank 𝓀[K] 𝓀[L] : Int)` is
   `v_normUnits_integerRingUniformizerFieldUnit_of_isSeparable K L`
   (M162.017), whose type is the statement constant unfolding to exactly this
   equation. Its instance arguments are this theorem's own instance
   hypotheses.
3. **Conclusion.** `unfold` exposes the target equation. Then
   `rw [inverseIntegerRingUniformizerFieldUnit, map_inv, hinv, hprime, neg_neg]`
   rewrites `inverseIntegerRingUniformizerFieldUnit L` to
   `(integerRingUniformizerFieldUnit L)⁻¹`, moves the inverse out of
   `normUnits K L` with `map_inv`, applies `hinv` and `hprime`, and turns
   `-(-(f : Int))` into `(f : Int)`. The goal becomes
   `(Module.finrank 𝓀[K] 𝓀[L] : Int) = (Module.finrank 𝓀[K] 𝓀[L] : Int)`,
   which `rw` closes by reflexivity.

The module has no auxiliary declarations. The local instance attribute on
`FractionRing.liftAlgebra` is scoped to this module. It is kept from the
source file (line 321) for fidelity, but this proof does not use it: a
development probe of the same module with the attribute line deleted also
compiled with no errors and no warnings.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean),
SHA-256 `b54bcd01a217ffc5fb905d410fe9ef64ebf87e5d7192509332cad827fc22c90e`.
The relevant lines are the file-level local instance attribute at line 321
and the theorem at lines 473–490 (docstring 473–474, statement 475–487, proof
487–490). The source proof is

```lean
  rw [inverseIntegerRingUniformizerFieldUnit, map_inv, v_inv,
    v_normUnits_integerRingUniformizerFieldUnit_of_isSeparable]
  simp only [neg_neg]
```

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparable` (M162.018) | `Langlands.NYLL.LocalClassFieldTheory.v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparable`, proving the published target |
| Same theorem's statement | Existing `v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparableStatement` |
| `LocalClassFieldTheory.v_normUnits_integerRingUniformizerFieldUnit_of_isSeparable` (M162.017), used | `Langlands.NYLL.LocalClassFieldTheory.v_normUnits_integerRingUniformizerFieldUnit_of_isSeparable`, imported |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v_inv` (M128.006), used | `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_inv`, imported |

Modifications by Worker 369 on 14 November 2026:

- the namespace gets the `Langlands.NYLL` prefix, and the source imports are
  replaced by the modules listed above;
- the theorem's type is the statement constant
  `v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparableStatement K L`
  instead of the equation it unfolds to, and the proof begins with `unfold`
  of that constant;
- the source rewrites with `v_inv` and with the M162.017 theorem directly;
  since both imported theorems now have statement constants as their types,
  the proof first states their instances as the local facts `hinv` and
  `hprime` and rewrites with those;
- the final `simp only [neg_neg]` becomes the last rewrite `neg_neg` of the
  same `rw`;
- every other declaration of the source file is omitted.

The theorem name, docstring, binders and the local instance attribute are
kept.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`; the attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`. Searches of the workspace, the
current Library, staging and shared drafts found no earlier proof of this
target.

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

This module proves only M162.018. The prime-element statement M162.017 is
proved in its own module, and M162.019 is outside this task.
