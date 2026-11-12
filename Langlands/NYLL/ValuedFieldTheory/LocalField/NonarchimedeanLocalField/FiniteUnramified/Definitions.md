# Finite unramified valued extensions: the class

This module extracts the single source declaration M161.001 from Naganori
Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteUnramified.lean`,
lines 32–44](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteUnramified.lean#L32-L44),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The adapted declaration
is the Prop-valued class
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension`.

## Exact source correspondence

| Original declaration | Adapted declaration | Source unit and lines |
| --- | --- | --- |
| `LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension` | `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension` | M161.001, docstring lines 32–35, class lines 36–44 |

The original reads:

```lean
class IsUnramifiedValuedExtension (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] : Prop where
  maximalIdeal_ramificationIdx_eq_one :
    (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] = 1
```

The adaptation keeps every instance parameter, their order, the field name
`maximalIdeal_ramificationIdx_eq_one`, its type and both docstrings. It makes
one change to the signature: the source places `K` and `L` in one universe
`u`, while the adaptation takes `(K : Type u) (L : Type v)`. The class body
never compares the two carriers, so the source class is exactly the
specialization `IsUnramifiedValuedExtension.{u, u}`. Independent universes
let the class be stated for supplied host fields such as
`F : PadicField.{u} p` and `E : PadicField.{v} p`.

## Meaning

All structures are supplied instances. `K` and `L` are fields with their own
`ValuativeRel`, topology and Mathlib `IsNonarchimedeanLocalField` structure;
`Algebra K L` is an arbitrary supplied finite-dimensional algebra. Nothing is
replaced by a canonical or chosen structure.

The notation comes from Mathlib's scoped `ValuativeRel` notation in
`Mathlib.Topology.Algebra.Valued.ValuativeRel`:

- `𝒪[K]` is `Valuation.integer (ValuativeRel.valuation K)`, the actual
  valuation ring `{x | v x ≤ 1}` of the supplied valuation, and likewise for
  `𝒪[L]`;
- `𝓂[L]` is `IsLocalRing.maximalIdeal ↥𝒪[L]`.

`Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)`
is Mathlib's compatibility of the two supplied valuations along the supplied
`algebraMap K L`. Through it, Mathlib's instance
`Valuation.HasExtension.instAlgebraInteger` gives `Algebra 𝒪[K] 𝒪[L]`. Its
`algebraMap` is the restriction of `algebraMap K L` to the two valuation
rings, and its scalar action is the field scalar action. The parameter
`Module.Finite 𝒪[K] 𝒪[L]` is finiteness for exactly this module structure.
The pinned source uses the same Mathlib instance: a lexical search of the
whole pinned NYLL source tree finds no other `Algebra 𝒪[K] 𝒪[L]` instance,
only `Module.Finite` instances for this pair.

The class field states that Mathlib's `Ideal.ramificationIdx` of
`𝓂[L]` over `𝒪[K]` is `1`. In this Mathlib, from
`Mathlib.RingTheory.RamificationInertia.Ramification`,
`Ideal.ramificationIdx (q : Ideal S) (R : Type*) [Algebra R S]` is the length
of `Sq ⧸ (q.under R).map (algebraMap R Sq)` over the localization
`Sq = Localization.AtPrime q` for prime `q`, and `0` for nonprime `q`. Here
`q = 𝓂[L]` is prime, so the field is the usual ramification index `e(L/K) = 1`
of the maximal ideal over the base valuation ring. Residue-degree, Galois and
Frobenius properties are not part of the class.

As in the source, the class is a `Prop` predicate. It contains no data and
installs no instance. It also does not assert that every finite extension is
unramified.

## Imports and reuse

The four direct imports are Mathlib modules:

| Import | Supplies |
| --- | --- |
| `Mathlib.NumberTheory.LocalField.Basic` | `IsNonarchimedeanLocalField` |
| `Mathlib.RingTheory.RamificationInertia.Ramification` | `Ideal.ramificationIdx` |
| `Mathlib.RingTheory.Valuation.Extension` | `Valuation.HasExtension` and the integer algebra instance |
| `Mathlib.Topology.Algebra.Valued.ValuativeRel` | the scoped notation `𝒪[·]`, `𝓂[·]` |

No NYLL source module is imported. The partition's incoming edges for M161
describe the whole source file's imports (`ResidueGalois`,
`ValuationExactSequence`, `IdealQuotients`). The class itself uses none of their
declarations. The focused check below establishes the smaller dependency set
for this definition only, as the partition permits for an early definition.

Reuse search: the current Library has no declaration of this predicate. The
host proposition
`Langlands.LocalClassField.NYLL.RamifiedGeometricNormalizationTransferStatement`
writes a premise of the same mathematical kind for supplied
`PadicField.TopologicalData`. That premise uses the explicit scalars
`PadicField.TopologicalData.relativeIntegerAlgebra` on the supplied integer
rings instead of this class and its Mathlib integer algebra. Comparing the two
premises is a separate bridge statement. Mathlib's `Algebra.FormallyUnramified`
(vanishing Kähler differentials) and `Algebra.Unramified` (formally unramified
and of finite type) are different ring-theoretic predicates, not this
ramification-index predicate, so the source class is ported, not replaced.

## Scope

This module contains only M161.001. The source theorems M161.002 onward,
including `unramifiedValuation_ramificationIdx_eq_one` and the residue-degree,
uniformizer, principal-unit and Galois consequences, are not ported here. No
proof, instance, supplied-data comparison, Artin-map normalization or
reciprocity statement is claimed.

## Development check

The module compiles in the approved Lean 4.34.0 / Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` environment
(`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`) with no errors or warnings.
Inspection of
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension`
reports an inductive declaration with universe parameters `u, v`. Its
dependencies use only `propext`, `Classical.choice` and `Quot.sound`. This
check is not independent review or publication.

## Source record and attribution

The original source is registered as
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The selected original file has SHA256
`b9c37585002a07b55997dd84ffdc7409fa5fee34fea04889196a4f617ddb909d`, matching
the partition inventory entry for M161. The attribution supplement is
registered as `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum was found in the project errata lookup.

The original copyright and author header is retained verbatim: Copyright (c)
2026 Naganori Yamaguchi (`https://github.com/n-yamaguchi-0729`), all rights
reserved; authors Naganori Yamaguchi (assisted by OpenAI Codex). The source
is released under Apache-2.0. The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are preserved unchanged.

Worker 8 extracted this declaration from the pinned original on
8 November 2026. Worker 8 prefixed the namespace with `Langlands.NYLL`,
generalized the carrier universes as described above, replaced the source
import list with the four Mathlib imports, and wrote this documentation. The
Lean header records these modifications. No private adaptation by another
worker was reused. The original uses Lean 4.35.0-rc2 and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. This extraction targets the
approved Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
