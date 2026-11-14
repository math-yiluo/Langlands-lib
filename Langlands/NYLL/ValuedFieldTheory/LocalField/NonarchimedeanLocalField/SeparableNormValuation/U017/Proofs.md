# Normalized valuation of the norm of the chosen prime element: proof

This module proves the theorem
`Langlands.NYLL.LocalClassFieldTheory.v_normUnits_integerRingUniformizerFieldUnit_of_isSeparable`.
Its type is the published proposition
`Langlands.NYLL.LocalClassFieldTheory.v_normUnits_integerRingUniformizerFieldUnit_of_isSeparableStatement K L`,
applied to the theorem's own parameters. This is the proof phase of source
unit M162.017 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m145-m168.md#m162).

Mathematically: for a finite separable extension `L / K` of nonarchimedean
local fields, with the valuation of `L` extending that of `K` and `𝒪[L]` the
integral closure of `𝒪[K]` in `L`, the field norm of the chosen prime element
`ϖ_L` of `L` has NYLL-normalized value `v_K(N_{L/K}(ϖ_L)) = -f`, where
`f = [𝓀[L] : 𝓀[K]]` is the residue degree. (NYLL's `v` gives a prime element
the value `-1`.)

## Target and binders

The theorem's complete telescope and conclusion are

```lean
open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

attribute [local instance] FractionRing.liftAlgebra

theorem v_normUnits_integerRingUniformizerFieldUnit_of_isSeparable
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    v_normUnits_integerRingUniformizerFieldUnit_of_isSeparableStatement K L
```

The binders before the colon are the published statement's parameters in the
same order, with the same binder kinds and names. The statement unfolds to

```lean
v K (Additive.ofMul
    (normUnits K L (integerRingUniformizerFieldUnit L))) =
  -(Module.finrank 𝓀[K] 𝓀[L] : Int)
```

## Imports and dependencies

The direct imports are published Library modules:

| Module (under `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField`) | Used declaration | Source unit |
| --- | --- | --- |
| `SeparableNormValuation.UniformizerNorm.Statements` | the target statement | M162.017 (statement) |
| `SeparableNormValuation.U016.Proofs` | `Langlands.NYLL.LocalClassFieldTheory.relNorm_maximalIdeal_eq_pow_residue_finrank` | M162.016 |
| `IdealQuotients.U005.Proofs` | `Langlands.NYLL.LocalFieldTheory.chosenIntegerRingUniformizer_irreducible` | M133.005 |
| `IdealQuotients.U006.Proofs` | `Langlands.NYLL.LocalFieldTheory.chosenIntegerRingUniformizer_maximalIdeal_eq` | M133.006 |
| `IdealQuotients.U015.Proofs` | `Langlands.NYLL.LocalFieldTheory.v_integerRingIrreducibleFieldUnit` | M133.015 |
| `IdealQuotients.U022.Proofs` | `Langlands.NYLL.LocalFieldTheory.maximalIdeal_pow_eq_span_uniformizer_pow` | M133.022 |
| `Basic.U004.Proofs` | `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_mul` | M128.004 |
| `Basic.U005.Proofs` | `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_one` | M128.005 |
| `Basic.U019.Proofs` | `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v_integerUnitsToFieldUnits` | M128.019 |

Two source dependencies are not imported because their proofs are not yet in
the Library:

- **M128.008 `v_pow`.** The module proves its statement as the private
  theorem `v_pow_of_v_mul_v_one`:
  `v K (Additive.ofMul (x ^ n)) = (n : Int) * v K (Additive.ofMul x)` for
  `x : Kˣ` and `n : Nat`. The statement is the same as the published target
  `v_powStatement` (M128.008) after its `∀`-binders are instantiated. The
  proof is induction on `n`. The zero case rewrites with `pow_zero`, `v_one K`,
  `Nat.cast_zero` and `zero_mul`. The successor case rewrites with
  `pow_succ`, `v_mul K (x ^ n) x`, the induction hypothesis, `Nat.cast_succ`,
  `add_mul` and `one_mul`. This follows the source proof (`Basic.lean`, lines
  112–122), whose successor case rewrites the cast with `Nat.cast_add_one`
  and closes with `ring` instead of the last three rewrites. The theorem
  is `private`, so it does not clash with the later published `v_pow`.
- **M133.018 `v_integerRingUniformizerFieldUnit`.** Its source proof
  (`IdealQuotients.lean`, lines 265–272) is the single term
  `v_integerRingIrreducibleFieldUnit K (chosenIntegerRingUniformizer K)
  (chosenIntegerRingUniformizer_irreducible K) (integerRingUniformizerFieldUnit K) rfl`.
  The proof uses this term directly as the local fact `hprime` (step 6
  below). `rfl` works because `integerRingUniformizerFieldUnit K` is
  `Units.mk0` of the coercion of `chosenIntegerRingUniformizer K`.

The Mathlib results used are:

- `IsIntegralClosure.finite` (`Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`,
  line 175): the integral closure of an integrally closed Noetherian domain in a
  finite separable extension of its fraction field is a finite module;
- `Ideal.spanNorm_singleton` (`Mathlib/RingTheory/Ideal/Norm/RelNorm.lean`,
  line 82): `spanNorm R (span {r}) = span {Algebra.intNorm R S r}`;
- `Ideal.span_singleton_eq_span_singleton` (`Mathlib/RingTheory/Ideal/Span.lean`,
  line 188): in a domain, two principal ideals are equal iff their generators
  are associated;
- `Algebra.algebraMap_intNorm` (`Mathlib/RingTheory/IntegralClosure/IntegralRestrict.lean`,
  line 410): `algebraMap A K (Algebra.intNorm A B x) = Algebra.norm K (algebraMap B L x)`;
- `Units.ext`, `map_mul`, `add_zero`, `mul_neg_one`.

## Implemented proof

1. **Finiteness.** A `let` binding introduces the instance
   `Module.Finite 𝒪[K] 𝒪[L]` as `IsIntegralClosure.finite 𝒪[K] K L 𝒪[L]`. Its
   hypotheses are found by instance search: `𝒪[K]` is a discrete valuation
   ring, hence integrally closed and Noetherian, `K` is its fraction field,
   `L / K` is finite separable, and `𝒪[L]` is the integral closure by
   hypothesis. This instance is the last hypothesis of the M162.016 theorem.
   Then `f` is bound to `Module.finrank 𝓀[K] 𝓀[L]`.
2. **Ideal equation `hspan`.** A `calc` chain proves
   `span {intNorm 𝒪[K] 𝒪[L] ϖ_L} = span {ϖ_K ^ f}` in `𝒪[K]`, where `ϖ_L`, `ϖ_K`
   are `chosenIntegerRingUniformizer L`, `chosenIntegerRingUniformizer K`:
   - `span {intNorm ϖ_L} = relNorm 𝒪[K] (span {ϖ_L})` is the symmetric form of
     `Ideal.spanNorm_singleton`; `relNorm` applied to an ideal is `spanNorm`
     by definition, and `exact` accepts this;
   - `relNorm 𝒪[K] (span {ϖ_L}) = relNorm 𝒪[K] 𝓂[L]` is `rw` with the M133.006
     theorem `chosenIntegerRingUniformizer_maximalIdeal_eq L`
     (`𝓂[L] = span {ϖ_L}`);
   - `relNorm 𝒪[K] 𝓂[L] = 𝓂[K] ^ f` is `exact` with the M162.016 theorem
     `relNorm_maximalIdeal_eq_pow_residue_finrank K L`, whose type is the
     statement constant unfolding to exactly this equation;
   - `𝓂[K] ^ f = span {ϖ_K ^ f}` is the M133.022 theorem
     `maximalIdeal_pow_eq_span_uniformizer_pow K f`.
3. **A unit factor.** `Ideal.span_singleton_eq_span_singleton.mp hspan` gives
   that the two generators are associated: a unit `u : 𝒪[K]ˣ` with
   `intNorm 𝒪[K] 𝒪[L] ϖ_L * u = ϖ_K ^ f`.
4. **Equation of field units `hfieldUnits`.** The proof shows
   `normUnits K L (integerRingUniformizerFieldUnit L) * integerUnitsToFieldUnits K u
   = integerRingUniformizerFieldUnit K ^ f` in `Kˣ`. By `Units.ext` it is enough
   to compare values in `K`. Applying `algebraMap 𝒪[K] K` to the equation of
   step 3 and rewriting with `map_mul` and `Algebra.algebraMap_intNorm` turns
   the left factor into `Algebra.norm K (algebraMap 𝒪[L] L ϖ_L)`. A `change`
   states the goal in this form; it holds by unfolding `normUnits`
   (`Units.map (Algebra.norm K)`), `integerUnitsToFieldUnits`
   (`Units.map (algebraMap 𝒪[K] K)`), `integerRingUniformizerFieldUnit`
   (`Units.mk0` of the coerced uniformizer) and the value of a power of a
   unit; `change` accepts it, so the two forms agree definitionally, and
   `exact huField` closes the goal.
5. **Taking values.** `hvalue` applies `fun z => v K (Additive.ofMul z)` to
   `hfieldUnits`, and `change` puts it in beta-reduced form.
6. **Rewriting the values.** Three local facts are taken from the imported
   theorems, each of whose types is a statement constant that Lean unfolds
   when checking the ascribed type:
   - `hmul` from `v_mul K _ _` (M128.004): the value of the product is the sum
     of the values;
   - `hunit` from `v_integerUnitsToFieldUnits K u` (M128.019): the image of an
     integral unit has value `0`;
   - `hprime` from the M133.018 term above: `v K (Additive.ofMul
     (integerRingUniformizerFieldUnit K)) = -1`.

   Then `rw [hmul, hunit, add_zero, v_pow_of_v_mul_v_one, hprime] at hvalue`
   yields `v K (Additive.ofMul (normUnits K L (integerRingUniformizerFieldUnit L)))
   = (f : Int) * -1`.
7. **Conclusion.** `unfold` exposes the target equation, and
   `rw [hvalue, mul_neg_one]` closes it, since `f` is by definition
   `Module.finrank 𝓀[K] 𝓀[L]`.

The only auxiliary declaration is the private theorem
`v_pow_of_v_mul_v_one`. The `let` bindings are local to the proof, and the
local instance attribute on `FractionRing.liftAlgebra` is scoped to this
module. It is kept from the source file (line 321) for fidelity, but this
proof does not use it: a development probe of the same module with the
attribute line deleted also compiled with no errors and no warnings.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean),
SHA-256 `b54bcd01a217ffc5fb905d410fe9ef64ebf87e5d7192509332cad827fc22c90e`.
The relevant lines are the file-level local instance attribute at line 321
and the theorem at lines 412–471 (docstring 412–414, statement 415–427, proof
427–471). The theorem lies outside every `section`, and no `variable` is in
scope at that point. The helper `v_pow` is in the same snapshot's
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`, lines
112–122, and `v_integerRingUniformizerFieldUnit` is in
`.../NonarchimedeanLocalField/IdealQuotients.lean`, lines 262–272.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.v_normUnits_integerRingUniformizerFieldUnit_of_isSeparable` (M162.017) | `Langlands.NYLL.LocalClassFieldTheory.v_normUnits_integerRingUniformizerFieldUnit_of_isSeparable`, proving the published target |
| Same theorem's statement | Existing `v_normUnits_integerRingUniformizerFieldUnit_of_isSeparableStatement` |
| `LocalClassFieldTheory.relNorm_maximalIdeal_eq_pow_residue_finrank` (M162.016), used | Published, imported |
| `LocalFieldTheory.chosenIntegerRingUniformizer_irreducible` (M133.005), `chosenIntegerRingUniformizer_maximalIdeal_eq` (M133.006), `v_integerRingIrreducibleFieldUnit` (M133.015), `maximalIdeal_pow_eq_span_uniformizer_pow` (M133.022), used | Published `Langlands.NYLL.LocalFieldTheory.*`, imported |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v_mul` (M128.004), `v_one` (M128.005), `v_integerUnitsToFieldUnits` (M128.019), used | Published `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.*`, imported |
| `LocalFieldTheory.IsNonarchimedeanLocalField.v_pow` (M128.008), used | Private `v_pow_of_v_mul_v_one` in this module |
| `LocalFieldTheory.v_integerRingUniformizerFieldUnit` (M133.018), used | Its source proof term, inlined as `hprime` |

Modifications by Worker 369 on 14 November 2026:

- the namespace gets the `Langlands.NYLL` prefix, and the source imports are
  replaced by the published modules listed above;
- the theorem's type is the statement constant
  `v_normUnits_integerRingUniformizerFieldUnit_of_isSeparableStatement K L`
  instead of the equation it unfolds to, and the proof ends with `unfold` of
  that constant before the last rewrite;
- the M162.016 step is `exact relNorm_maximalIdeal_eq_pow_residue_finrank K L`
  instead of `simpa [f] using …`, since `simp` does not unfold the statement
  constant that is now that theorem's type;
- the source's single `rw [v_mul, v_integerUnitsToFieldUnits, add_zero, v_pow,
  v_integerRingUniformizerFieldUnit] at hvalue` becomes three local facts
  (`hmul`, `hunit`, `hprime`) and `rw [hmul, hunit, add_zero,
  v_pow_of_v_mul_v_one, hprime] at hvalue`, because the imported theorems
  have statement constants as their types and `v_pow` and M133.018 are
  replaced as described above;
- the final `simpa [f] using hvalue` becomes `rw [hvalue, mul_neg_one]`;
- every other declaration of the source file is omitted.

The theorem name, docstring, binders, the local instance attribute and the
steps through `hvalue` are kept.

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

This module proves only M162.017. The inverse-element statement M162.018 is
proved separately, and M162.019 is outside this task.
