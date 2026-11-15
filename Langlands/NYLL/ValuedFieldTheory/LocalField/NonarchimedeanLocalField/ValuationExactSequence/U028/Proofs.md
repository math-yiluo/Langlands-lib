# Valuation-ring units from field units of valuation zero: proofs (M134.028, M134.039, M134.040)

This module proves the three closed proposition targets of the published
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U028.Statements`
module, at the universe level `u`, in the namespace
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField`:

```lean
theorem integerUnitOfValuationMapZero_spec :
    integerUnitOfValuationMapZero_specStatement.{u}

theorem integerUnitsToFieldUnits_uniformizerUnitFactor :
    integerUnitsToFieldUnits_uniformizerUnitFactorStatement.{u}

theorem uniformizerUnitFactor_mul_uniformizer_zpow :
    uniformizerUnitFactor_mul_uniformizer_zpowStatement.{u}
```

These are the proof phases of M134.028, M134.039 and M134.040 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m134).
After the first two theorems the module also adds two explicit-telescope
`@[simp]` wrappers, `integerUnitOfValuationMapZero_spec_apply` and
`integerUnitsToFieldUnits_uniformizerUnitFactor_apply`, described in
[Simp attributes](#simp-attributes). No other declaration is added.

## Notation and sign convention

Throughout, `K : Type u` is a nonarchimedean local field: a field with
`[ValuativeRel K]`, `[TopologicalSpace K]` and Mathlib's
`[IsNonarchimedeanLocalField K]`, in this source order. `𝒪[K]` is its
valuation ring `Valuation.integer (ValuativeRel.valuation K)`, a subring of
`K`, and `integerUnitsToFieldUnits K : 𝒪[K]ˣ →* Kˣ` is the published
inclusion `Units.map (algebraMap 𝒪[K] K).toMonoidHom` (M128.016, module
`Basic.U016.Definitions`). For a field unit `x : Kˣ` write
`v(x) = valuationMap K (Additive.ofMul x) : ℤ`, where `valuationMap` is the
published additive map of `ValuationExactSequence.Definitions` (M134.002).

**Sign convention.** NYLL's `valuationMap` is the **negative** of the usual
normalized order: a prime element of `𝒪[K]` has value `-1`, and its inverse
has value `1`. This is recorded in the paired Markdown of the statement
module and in section 2.3 of the published audit
[`notes/reuse/nyll-finite-local-reciprocity-audit.md`](../../../../../../../notes/reuse/nyll-finite-local-reciprocity-audit.md).
Consequently a field unit `ϖ` with `hϖ : valuationMap K (Additive.ofMul ϖ) = 1`,
as in M134.039 and M134.040, is an **inverse uniformizer**: `ϖ⁻¹` is a
prime element of `𝒪[K]`. The source names (`uniformizerUnitFactor`,
`..._mul_uniformizer_zpow`) keep the word "uniformizer"; in usual terms the
decomposition `x = u * ϖ ^ v(x)` of M134.040 reads
`x = u * (ϖ⁻¹) ^ ord(x)`. None of the three proofs depends on the sign:
they only use the hypothesis `hϖ` through the published M134.037 theorem.

The data in the targets are the published definitions of
`ValuationExactSequence.U027.Definitions`:

- `integerUnitOfValuationMapZero K x hx : 𝒪[K]ˣ` (M134.027), for `x : Kˣ`
  and `hx : v(x) = 0`, whose value is the subtype element `⟨(x : K), _⟩` and
  whose inverse is `⟨(x⁻¹ : K), _⟩`;
- `uniformizerUnitFactor K ϖ hϖ x : 𝒪[K]ˣ` (M134.038), defined as
  `integerUnitOfValuationMapZero K (x / ϖ ^ v(x)) (uniformizerUnitFactorValuationZero K ϖ x hϖ)`,
  where `uniformizerUnitFactorValuationZero` is the published M134.037
  theorem (`ValuationExactSequence.U037.Proofs`) proving `v(x / ϖ ^ v(x)) = 0`.

The power `ϖ ^ v(x)` is the integer power in the group `Kˣ` and `/` is
division in `Kˣ`.

## Targets and binders

The three targets are, by their definitions in the statement module,

```lean
-- M134.028
∀ (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (x : Kˣ) (hx : valuationMap K (Additive.ofMul x) = 0),
    integerUnitsToFieldUnits K (integerUnitOfValuationMapZero K x hx) = x

-- M134.039
∀ (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) (x : Kˣ),
    integerUnitsToFieldUnits K (uniformizerUnitFactor K ϖ hϖ x) =
      x / ϖ ^ valuationMap K (Additive.ofMul x)

-- M134.040
∀ (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) (x : Kˣ),
    integerUnitsToFieldUnits K (uniformizerUnitFactor K ϖ hϖ x) *
        ϖ ^ valuationMap K (Additive.ofMul x) = x
```

In words: M134.028 says that the valuation-ring unit built from a field unit
`x` of valuation zero maps back to `x`; M134.039 says that the field unit
underlying the integer-unit factor of `x` is `x / ϖ ^ v(x)`; M134.040 says
that `x = u * ϖ ^ v(x)` with `u` that field unit. The binders are exactly
the source theorems' binders, in source order: the field `K`, its four
instance arguments, then `x` and `hx` (M134.028), or `ϖ`, `hϖ` and `x`
(M134.039 and M134.040). No hypothesis is added.

The sole direct import is the published `U028.Statements` module. Through
it the proofs use `U027.Definitions` (the two definitions above) and the
published M134.037 proof module `U037.Proofs`, which `U027.Definitions`
imports because the body of `uniformizerUnitFactor` names that theorem.

## Implemented proofs

### M134.028 `integerUnitOfValuationMapZero_spec`

```lean
intro K _ _ _ _ x hx
ext
rfl
```

1. `intro K _ _ _ _ x hx` introduces the seven binders. The goal is
   `integerUnitsToFieldUnits K (integerUnitOfValuationMapZero K x hx) = x`
   in `Kˣ`.
2. `ext` applies the extensionality lemma for units (`Units.ext`) and
   reduces the goal to the equality in `K` of the underlying elements,
   `↑(integerUnitsToFieldUnits K (integerUnitOfValuationMapZero K x hx)) = ↑x`.
3. `rfl` closes this goal by definitional unfolding: the value of
   `Units.map f u` is `f ↑u`; here `f` is the algebra map of the subring
   `𝒪[K]` into `K`, which is the subtype inclusion, and `↑u` is the
   subtype element `⟨(x : K), _⟩`, so both sides are `(x : K)`.

### M134.039 `integerUnitsToFieldUnits_uniformizerUnitFactor`

```lean
intro K _ _ _ _ ϖ hϖ x
exact integerUnitOfValuationMapZero_spec K
  (x / ϖ ^ valuationMap K (Additive.ofMul x))
  (uniformizerUnitFactorValuationZero K ϖ x hϖ)
```

1. `intro K _ _ _ _ ϖ hϖ x` introduces the eight binders.
2. The term applies the M134.028 theorem just proved to `K` (its instance
   arguments are found by instance resolution), to the field unit
   `x / ϖ ^ v(x)` and to the proof `uniformizerUnitFactorValuationZero K ϖ x hϖ`
   (M134.037) that this unit has valuation zero. Its type is
   `integerUnitsToFieldUnits K (integerUnitOfValuationMapZero K (x / ϖ ^ v(x)) _) = x / ϖ ^ v(x)`.
   By the definition of `uniformizerUnitFactor` (M134.038) this is
   definitionally the goal, so `exact` accepts it.

### M134.040 `uniformizerUnitFactor_mul_uniformizer_zpow`

```lean
intro K _ _ _ _ ϖ hϖ x
rw [integerUnitsToFieldUnits_uniformizerUnitFactor]
simp [div_eq_mul_inv, mul_assoc]
```

1. `intro K _ _ _ _ ϖ hϖ x` introduces the eight binders. The goal is
   `integerUnitsToFieldUnits K (uniformizerUnitFactor K ϖ hϖ x) * ϖ ^ v(x) = x`.
2. `rw [integerUnitsToFieldUnits_uniformizerUnitFactor]` rewrites with the
   M134.039 theorem just proved. `rw` unfolds its closed statement to the
   universally quantified equation, turns the quantified variables into
   metavariables, and instantiates them by matching the left-hand side with
   the goal. The goal becomes `x / ϖ ^ v(x) * ϖ ^ v(x) = x`.
3. `simp [div_eq_mul_inv, mul_assoc]` closes the goal by group
   cancellation. In a development check, `simp?` reported the equivalent
   call `simp only [div_eq_mul_inv, mul_assoc, inv_mul_cancel, mul_one]`:
   the goal is rewritten to `x * ((ϖ ^ v(x))⁻¹ * ϖ ^ v(x)) = x`, then to
   `x * 1 = x` and `x = x`. The `@[simp]` wrapper for M134.039 declared
   earlier in this module is in the default simp set, but no
   `uniformizerUnitFactor` term remains after step 2, so it is not used.

The development check reports that each of the three theorems has the
single level parameter `u` and uses only `propext`, `Classical.choice` and
`Quot.sound`, all already used by the imported definitions and Mathlib.
Since the M134.040 proof uses the M134.039 theorem, which uses the M134.028
theorem, the axiom report for M134.040 covers all three proofs.

## Simp attributes

The source marks M134.028 and M134.039 `@[simp]`. Here the theorems with
the required names have the closed statements as their types. `simp` does
not unfold a closed statement definition, so that attribute would not give a
usable simp lemma on them: a development check confirmed that
`simp only [integerUnitOfValuationMapZero_spec]` and
`simp only [integerUnitsToFieldUnits_uniformizerUnitFactor]` make no progress
on the corresponding goals. The two theorems therefore carry no attribute.
Instead, right after each of them, the module adds a wrapper with the
source theorem's explicit binder telescope and the `@[simp]` attribute,
proved by applying the exact closed theorem to its arguments:

```lean
@[simp]
theorem integerUnitOfValuationMapZero_spec_apply (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (x : Kˣ) (hx : valuationMap K (Additive.ofMul x) = 0) :
    integerUnitsToFieldUnits K (integerUnitOfValuationMapZero K x hx) = x :=
  integerUnitOfValuationMapZero_spec K x hx

@[simp]
theorem integerUnitsToFieldUnits_uniformizerUnitFactor_apply (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) (x : Kˣ) :
    integerUnitsToFieldUnits K (uniformizerUnitFactor K ϖ hϖ x) =
      x / ϖ ^ valuationMap K (Additive.ofMul x) :=
  integerUnitsToFieldUnits_uniformizerUnitFactor K ϖ hϖ x
```

Their statements are, word for word, the source statements of M134.028 and
M134.039 (source lines 275–278 and 438–442), so importing this module
restores the source simp behavior. The same development check confirmed
that plain `simp` proves the M134.028 equation and the M134.040 equation
for given arguments, and that `simp only` with either wrapper closes the
corresponding equation. The wrapper names, with the suffix `_apply`, are
new and follow the precedent of
`Langlands/NYLL/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient/U015/Proofs.lean`;
they are not source names and are not second copies of a required theorem.
A consumer porting a source `simp only [integerUnitsToFieldUnits_uniformizerUnitFactor]`
can use the wrapper in that call, or `rw` with the exact theorem.

## Original passages and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean`.
The passages are

- [lines 272–281](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean#L272-L281)
  (M134.028): docstring at 272–273, `@[simp]` at 274, signature at
  275–278, proof `ext` / `rfl` at 279–280, followed by a blank line;
- [lines 435–445](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean#L435-L445)
  (M134.039): docstring at 435–436, `@[simp]` at 437, signature at
  438–442, term proof
  `integerUnitOfValuationMapZero_spec K (x / ϖ ^ valuationMap K (Additive.ofMul x)) (uniformizerUnitFactorValuationZero K ϖ x hϖ)`
  at 443–445;
- [lines 447–454](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean#L447-L454)
  (M134.040): docstring at 447, signature at 448–452, proof
  `rw [integerUnitsToFieldUnits_uniformizerUnitFactor]` /
  `simp [div_eq_mul_inv, mul_assoc]` at 453–454.

They lie in the `LocalFieldTheory` namespace and its `noncomputable section`
(source lines 20–24), with `universe u`, in the inner
`IsNonarchimedeanLocalField` namespace whose
`open scoped ValuativeRel WithZero` directive (lines 26–28) is kept here.
The complete original file is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean`;
it was read and its SHA-256 hash verified as
`8a8515596e4388771957f2c4c484e8c86767236ab79f973fa405df2d34e02908`, the hash
recorded in the partition, which records no patch10 change to this module.

| Original declaration | Adapted declaration in `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField` |
| --- | --- |
| `integerUnitOfValuationMapZero_spec` (theorem, `@[simp]`) | `integerUnitOfValuationMapZero_spec` (theorem, no attribute), proving the published target |
| — | `integerUnitOfValuationMapZero_spec_apply` (new `@[simp]` wrapper) |
| `integerUnitsToFieldUnits_uniformizerUnitFactor` (theorem, `@[simp]`) | `integerUnitsToFieldUnits_uniformizerUnitFactor` (theorem, no attribute), proving the published target |
| — | `integerUnitsToFieldUnits_uniformizerUnitFactor_apply` (new `@[simp]` wrapper) |
| `uniformizerUnitFactor_mul_uniformizer_zpow` (theorem) | `uniformizerUnitFactor_mul_uniformizer_zpow` (theorem), proving the published target |
| Statements of the three theorems | Existing `…Statement` definitions of `U028.Statements` |
| `integerUnitOfValuationMapZero` (M134.027), `uniformizerUnitFactor` (M134.038) | Existing published definitions of `U027.Definitions` |
| `uniformizerUnitFactorValuationZero` (M134.037), used in the M134.039 term | Existing published theorem of `U037.Proofs` |
| `integerUnitsToFieldUnits`, `valuationMap` | Existing published definitions |

Modifications by Worker 127 on 15 November 2026 are:

- add the `Langlands.NYLL` namespace prefix and replace the source imports
  with the sole `U028.Statements` import;
- give each required theorem the published closed statement as its type and
  introduce its binders with `intro`; the M134.039 term proof becomes the
  same term under `intro … ; exact`;
- keep the source proof steps otherwise unchanged: `ext` / `rfl`, the source
  term, and the source `rw [integerUnitsToFieldUnits_uniformizerUnitFactor]` /
  `simp [div_eq_mul_inv, mul_assoc]`; the names in them now denote the
  closed theorems of this module and the published M134.037 theorem, applied
  to the same arguments (in the `rw` the arguments are found by unification
  as in the source);
- move the source `@[simp]` attributes of M134.028 and M134.039 to the two
  new explicit-telescope wrappers, as explained above;
- omit the source `noncomputable section`, which theorems do not need, and
  all other source declarations.

The theorem names and docstrings are kept.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
Additional attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Searches of the Library, staging and shared drafts found no earlier proof
port of these three theorems.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`,
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. A
development check compiled the module with no diagnostics. This check does
not establish independent semantic acceptance or Integrator publication.

## Attribution and boundary

The original copyright and author header is preserved verbatim:
copyright 2026 Naganori Yamaguchi, author “Naganori Yamaguchi (assisted
by OpenAI Codex)”, released under Apache-2.0. The Lean file carries the
dated modification record. Worker 127 adapted these proofs directly from
the pinned original and wrote this companion; Worker 85, who routed the
task, had replayed the same source proofs privately, and their task notes
were consulted. No other code or reused draft was supplied. The published
`U028.Statements`, `U027.Definitions` and `U037.Proofs` modules, all other
imported Library modules and their paired Markdown are used unchanged.

The unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) remain in the Library
and are byte-identical to the retained originals. Their SHA-256 hashes are
respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No Mathlib code is copied into this file; Mathlib lemmas are only used by
name.

This module proves only M134.028, M134.039 and M134.040 (plus the two
wrappers). It does not publish M134.041 or any other M134 theorem.
