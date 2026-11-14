# NYLL M138.026: module finiteness of integer rings from integral closure

This module proves the published Library proposition
`Langlands.NYLL.LocalFieldTheory.integerRing_moduleFinite_of_isIntegralClosureStatement`
by the theorem
`Langlands.NYLL.LocalFieldTheory.integerRing_moduleFinite_of_isIntegralClosure`.
The theorem's type is exactly that proposition applied to its source
parameters, `integerRing_moduleFinite_of_isIntegralClosureStatement K L`.

Its direct imports are the published
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension.ModuleFiniteStatement`
and the Mathlib module `Mathlib.RingTheory.DedekindDomain.IntegralClosure`,
which is one of the original source file's imports and provides
`IsIntegralClosure.finite`. The published Statement Lean/Markdown pair and
its imported chain remain unchanged.

## Target and parameters

The theorem has the explicit types `K L : Type u` and, in the order of the
statement, the instance hypotheses
`[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]`,
`[Field L] [ValuativeRel L] [Algebra K L] [FiniteDimensional K L]`,
`[Algebra.IsSeparable K L]`,
`[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`
and `[IsIntegralClosure 𝒪[L] 𝒪[K] L]`. Like the statement, it has one
universe parameter `u`. Unfolding the published proposition gives
`Module.Finite 𝒪[K] 𝒪[L]`, finiteness of the integer ring of `L` as a module
over the integer ring of `K`, for the canonical integer-ring algebra of the
valuation extension.

## Implemented proof

The complete proof body is the term

```lean
  IsIntegralClosure.finite 𝒪[K] K L 𝒪[L]
```

Mathlib's `IsIntegralClosure.finite A K L C` states that the integral closure
`C` of an integrally closed Noetherian domain `A` in a finite separable
extension `L` of its fraction field `K` is a finite `A`-module. Here
`A = 𝒪[K]` and `C = 𝒪[L]`. The hypotheses `FiniteDimensional K L`,
`Algebra.IsSeparable K L` and `IsIntegralClosure 𝒪[L] 𝒪[K] L` are the
theorem's own instance arguments. The remaining requirements of
`IsIntegralClosure.finite` (that `𝒪[K]` is a Noetherian, integrally closed
domain with fraction field `K`, and the algebra and scalar-tower structures
among `𝒪[K]`, `𝒪[L]`, `K` and `L`) are found by instance search in the
imported Mathlib; in particular, `Mathlib.NumberTheory.LocalField.Basic`
gives `IsDiscreteValuationRing 𝒪[K]` from `IsNonarchimedeanLocalField K`.
No local instance is declared for them. The resulting
type `Module.Finite 𝒪[K] 𝒪[L]` is the published proposition after the
elaborator unfolds the statement definition.

Apart from stating the type as the published proposition, this is the
original declaration verbatim, including its docstring. No auxiliary
declaration, extra hypothesis or instance is introduced. The development
check reports no errors or warnings, the single universe parameter `u`, and
only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.LocalFieldTheory.integerRing_moduleFinite_of_isIntegralClosureStatement`
  in ResidueExtension.ModuleFiniteStatement, with that module's Mathlib
  imports.
- Mathlib's `IsIntegralClosure.finite` from
  `Mathlib.RingTheory.DedekindDomain.IntegralClosure`, and the Mathlib
  instances that instance search supplies for its hypotheses.

No other NYLL or project proof is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean:333–343`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean#L333-L343).
Lines 333–335 are the docstring, lines 336–342 the signature and line 343
the proof. The enclosing `namespace LocalFieldTheory` (line 26) has
`noncomputable section` (28), `universe u` (30) and
`open scoped ValuativeRel` (32). The original imports include
`Mathlib.RingTheory.DedekindDomain.IntegralClosure` (line 15). The
[public partition](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m138)
places this theorem at M138.026 (source start line 336). The whole-file
SHA-256 is
`09a3886306e3d31336cebf5df8f2384b06c3f33afd045b4492568f31d3a6bc06`,
recomputed by Worker 395 on 14 November 2026 UTC from the retained snapshot.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| Asserted type of `integerRing_moduleFinite_of_isIntegralClosure` (M138.026) | Published `integerRing_moduleFinite_of_isIntegralClosureStatement` in ResidueExtension.ModuleFiniteStatement |
| Proof `integerRing_moduleFinite_of_isIntegralClosure` | This theorem of the same adapted name in ResidueExtension.U026.Proofs |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the published ModuleFiniteStatement import and the one
original Mathlib import the proof needs, keeps the `noncomputable section`,
`universe u`, `open scoped ValuativeRel` and the docstring, and states the
theorem's type as the published proposition applied to `K L`. The proof is
unchanged.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 395's dated modification
record. Worker 395 extracted this proof directly from the pinned original and
the published statement. No unpublished project draft was reused, and there
are no project coauthors.

The unchanged inherited
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation is separate from acceptance. Publication under
`lean.proof@1` requires the Lake build, kernel and exact-target checks,
unchanged statement and dependency checks, independent semantic review and
Integrator publication.

This proof covers only M138.026. The other M138 units, including M138.007,
are separate work.
