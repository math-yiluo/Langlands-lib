# Ramification index times the canonical residue degree: statement

This module exports the closed proposition
`Langlands.NYLL.LocalFieldTheory.maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrankStatement`.
For a finite extension whose integer ring is finite over the base integer ring, the actual maximal-ideal ramification index times the canonical residue-field degree equals the field-extension degree.
This is a statement target; this module supplies no proof of it.

## Exact proposition and hypotheses

```lean
def maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrankStatement : Prop :=
  ∀ (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]],
    Ideal.ramificationIdx' (𝓂[K] : Ideal 𝒪[K]) (𝓂[L] : Ideal 𝒪[L]) *
      Module.finrank 𝓀[K] 𝓀[L] =
        Module.finrank K L
```

The first two binders are the explicit `(K L : Type u)`. They are followed,
in order, by the instance binders `[Field K] [ValuativeRel K]
[TopologicalSpace K] [IsNonarchimedeanLocalField K]`, then the same four for
`L`, and `[Algebra K L]`. The next binders are `[FiniteDimensional K L]`,
`[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`
and `[Module.Finite 𝒪[K] 𝒪[L]]`, in that order.
No separability, integral-closure or Galois hypothesis is added.

The declaration has only the source universe parameter `u`; both fields have
type `Type u`. It has no outer field or instance parameters. Every source
parameter is quantified inside the proposition. The notation `𝒪[F]` denotes
`Valuation.integer (ValuativeRel.valuation F)`, `𝓂[F]` its maximal ideal, and
`𝓀[F]` its residue field, all from Mathlib's scoped `ValuativeRel` notation.
The residue extension uses the canonical algebra induced by the supplied
valuation extension. The displayed ideal invariant is kept in the precise
source spelling, including the prime on `Ideal.ramificationIdx'` where present.

## Published dependencies and reuse

The focused imports are:

- `Mathlib.NumberTheory.LocalField.Basic`.
- `Mathlib.NumberTheory.RamificationInertia.Ramification`.
- `Mathlib.RingTheory.Valuation.Extension`.

They supply Mathlib's `IsNonarchimedeanLocalField`, the displayed ideal
invariants and the canonical integer-ring and residue-field algebra structures
from `Valuation.HasExtension`. No NYLL bookkeeping instance or replacement
algebra structure is introduced. The source module's other declarations and
imports are unnecessary for this proposition.

The source statements were checked against the existing NYLL modules and the
relevant Mathlib ramification/inertia declarations before adding this target.
Mathlib's `Ideal.inertiaDeg_eq_of_isMaximal` identifies quotient-field degrees,
and `Ideal.sum_ramification_inertia_eq_finrank` is a sum over primes over an
ideal. Those are useful proof ingredients rather than the complete source
local-field targets with the displayed telescopes. M161.001's existing class
projection supplies the conclusion of M161.002 under its class hypothesis;
this task still provides the explicitly requested closed target with every
source binder. No unit is discharged by a replacement declaration.

## Source correspondence

The original is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean#L382-L395)
at pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The retained original is readable at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean`.
The complete source file has SHA-256 `09a3886306e3d31336cebf5df8f2384b06c3f33afd045b4492568f31d3a6bc06`.

| Unit | Original declaration | Source lines | Adapted declaration |
| --- | --- | --- | --- |
| M138.029 | `LocalFieldTheory.maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank` | 382–395 (theorem starts at 384) | `Langlands.NYLL.LocalFieldTheory.maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrankStatement` |

The source declares `universe u` at line 30.
The theorem's telescope and conclusion are copied from its source signature;
its proof is omitted. This unit is listed in the public NYLL declaration
partition, `notes/reuse/nyll-public-port/m121-m144.md`.

Worker 320 made these changes on 14 November 2026:

1. Prefix the original namespace with `Langlands.NYLL` and append `Statement`
   to the source theorem name.
2. Replace the theorem and its proof by the displayed `def ... : Prop`.
   The complete source type is placed under `∀`; explicit binders remain
   explicit, instance binders remain instance-implicit, and their order,
   universe and conclusion are unchanged.
3. Replace the source imports by the focused published dependencies above.
4. Omit the source's `noncomputable section`, which is unnecessary for a
   proposition definition, and replace the whole-file overview by a focused
   statement overview. Retain `universe u` and `open scoped ValuativeRel`.
5. Keep the original copyright/license/author header verbatim and add the
   modification record.

No source proof or another worker's draft is reused. No other source unit is
ported in this module. The separate proof tasks are owned by the dependent
NYLL program; this target makes no host reciprocity or class-formation claim.

## Provenance and license

The original is registered as `external-lean-reuse-snapshots-2026-10-21`, with
content fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The published Apache-2.0 [LICENSE](../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../licenses/NYLL/NOTICE) remain unchanged, with
SHA-256 values `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The Lean header retains copyright 2026 Naganori Yamaguchi and authors
Naganori Yamaguchi (assisted by OpenAI Codex).

## Focused check

The project Lean service compiled and inspected this exact declaration in
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Compilation succeeded with zero
errors and zero warnings. Inspection reported kind `definition`, exactly the
level parameter `[u]`, and `statement_returns_prop: true`; the reported axioms
were only `propext`, `Classical.choice` and `Quot.sound`. The signature was
extracted directly from the pinned source and checked against the displayed
closed quantification, including every instance binder and its order.
