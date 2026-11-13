# Separability of the fraction fields of valuation integer rings: proof

This module proves the theorem
`Langlands.NYLL.LocalClassFieldTheory.fractionRing_integerRing_isSeparable`.
Its type is the published proposition
`Langlands.NYLL.LocalClassFieldTheory.fractionRing_integerRing_isSeparableStatement K L`,
applied to the theorem's own parameters. This is the proof phase of source
unit M162.015 in the
[NYLL partition](../../../../../../../notes/reuse/nyll-public-port/m145-m168.md#m162).
The proof uses no source helper and no other NYLL declaration.

## Target and binders

The theorem's complete telescope and conclusion are

```lean
open scoped ValuativeRel

attribute [local instance] FractionRing.liftAlgebra

theorem fractionRing_integerRing_isSeparable
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L]
    [Algebra K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)] :
    fractionRing_integerRing_isSeparableStatement K L
```

The binders before the colon are the published statement's parameters in the
same order, with the same binder kinds and names. The published statement
unfolds to

```lean
Algebra.IsSeparable (FractionRing 𝒪[K]) (FractionRing 𝒪[L])
```

where `𝒪[K]` is `Valuation.integer (ValuativeRel.valuation K)` and the
algebra structure `Frac 𝒪[K] → Frac 𝒪[L]` is
`FractionRing.liftAlgebra 𝒪[K] (FractionRing 𝒪[L])`
(`Mathlib/RingTheory/Localization/FractionRing.lean`, line 769). The proof
module registers the same local instance attribute on
`FractionRing.liftAlgebra` as the statement module, so instance synthesis in
the proof produces this algebra structure. The underlying `𝒪[K]`-algebra
structure on `𝒪[L]` is Mathlib's `Valuation.HasExtension.instAlgebraInteger`
(`Mathlib/RingTheory/Valuation/Extension.lean`, line 119).

The sole direct import is the published module
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation.U015.Statements`.
Its Mathlib imports supply the whole API used below, including the
`IsFractionRing` instance of step 1.

## Implemented proof

The proof is the source proof, kept unchanged.

1. **`K` and `L` are fraction fields of their integer rings.** Mathlib's
   instance `ValuationRing.instIsFractionRingInteger`
   (`Mathlib/RingTheory/Valuation/ValuationRing.lean`, line 464) gives
   `IsFractionRing v.integer F` for every valuation `v` on a field `F`: every
   element of `F` or its inverse has valuation at most one. Applied to
   `ValuativeRel.valuation K` and `ValuativeRel.valuation L`, it makes `K` a
   fraction field of `𝒪[K]` and `L` a fraction field of `𝒪[L]`, with the
   subring algebra structures `𝒪[K] → K` and `𝒪[L] → L`. A development probe
   with `#synth` identified this instance in the approved environment.
2. **Canonical isomorphisms.** `FractionRing.algEquiv 𝒪[K] K` and
   `FractionRing.algEquiv 𝒪[L] L` (`FractionRing.lean`, line 793) are the
   canonical algebra isomorphisms `Frac 𝒪[K] ≃ₐ[𝒪[K]] K` and
   `Frac 𝒪[L] ≃ₐ[𝒪[L]] L`. Their inverses, as ring isomorphisms, are
   `e₁ : K ≃+* Frac 𝒪[K]` and `e₂ : L ≃+* Frac 𝒪[L]`.
3. **Transport of separability.** `Algebra.IsSeparable.of_equiv_equiv`
   (`Mathlib/FieldTheory/Separable.lean`, line 740) turns
   `Algebra.IsSeparable K L` into `Algebra.IsSeparable (Frac 𝒪[K]) (Frac 𝒪[L])`,
   given ring isomorphisms `e₁`, `e₂` such that
   `(algebraMap (Frac 𝒪[K]) (Frac 𝒪[L])).comp e₁ = e₂.comp (algebraMap K L)`.
   The proof `apply`s this lemma to the goal; `apply` unfolds the statement
   constant to its `Algebra.IsSeparable` body. The separability of `L / K` is
   the theorem's hypothesis, found by instance synthesis.
4. **The commuting square.** After `ext x`, the remaining goal is
   `algebraMap (Frac 𝒪[K]) (Frac 𝒪[L]) (e₁ x) = e₂ (algebraMap K L x)`. This
   is exactly `IsFractionRing.algEquiv_commutes e₁ e₂ x`
   (`FractionRing.lean`, line 308), applied with `A = 𝒪[K]`, `B = 𝒪[L]`,
   `K₁ = K`, `K₂ = Frac 𝒪[K]`, `L₁ = L` and `L₂ = Frac 𝒪[L]`. Its scalar-tower
   hypotheses are Mathlib instances: `𝒪[K] → 𝒪[L] → L` is
   `Valuation.HasExtension.instIsScalarTowerInteger` (`Extension.lean`,
   line 141), `𝒪[K] → K → L` is the subring scalar tower,
   `𝒪[K] → 𝒪[L] → Frac 𝒪[L]` is the localization scalar tower and
   `𝒪[K] → Frac 𝒪[K] → Frac 𝒪[L]` is the instance
   `FractionRing.instIsScalarTower` (`FractionRing.lean`, lines 785–786),
   which is stated for the `liftAlgebra` structure. A development probe with
   `#synth` identified these instances.

No auxiliary declaration, `let` binding or global instance is introduced. The
local instance attribute on `FractionRing.liftAlgebra` is scoped to this
module.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean),
SHA-256 `b54bcd01a217ffc5fb905d410fe9ef64ebf87e5d7192509332cad827fc22c90e`.
The relevant lines are the file-level local instance attribute at line 321
and the theorem at lines 371–387 (docstring 371–372, statement 373–380,
proof 380–387). The theorem lies outside every `section`, and no `variable`
is in scope at that point. The complete pinned file was read.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.fractionRing_integerRing_isSeparable` (M162.015) | `Langlands.NYLL.LocalClassFieldTheory.fractionRing_integerRing_isSeparable`, proving the published target |
| Same theorem's statement | Existing `fractionRing_integerRing_isSeparableStatement` |

Modifications by Worker 173 on 13 November 2026:

- the namespace gets the `Langlands.NYLL` prefix, and the source imports are
  replaced by the sole U015 Statements import;
- the theorem's type is the statement constant
  `fractionRing_integerRing_isSeparableStatement K L` instead of the
  `Algebra.IsSeparable` proposition it unfolds to;
- every other declaration of the source file is omitted.

The theorem name, docstring, binders, the local instance attribute and every
proof step are kept. The upstream proof needed no change in the approved
environment. In the source the `IsFractionRing` instances of step 1 come
through the NYLL imports; here the same Mathlib instance arrives through the
statement module's Mathlib imports.

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
Codex)”, released under Apache-2.0. The Lean file carries Worker 173's dated
modification record. Worker 173 adapted this proof directly from the pinned
original and wrote this companion. Worker 85's statement is used unchanged;
the imported statement module and its paired Markdown remain frozen.

The unchanged [LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are byte-identical to the
retained originals, with SHA-256 hashes
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. No
Mathlib code is copied into this file.

This module proves only M162.015. The relative-norm formula for the maximal
ideal of a local-field extension (M162.016), which uses this theorem, belongs
to the separate U016 proof.
