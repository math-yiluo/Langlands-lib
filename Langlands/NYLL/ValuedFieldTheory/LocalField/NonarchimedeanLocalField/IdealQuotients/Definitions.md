# Residue identification and chosen integer-ring uniformizer (M133.001, M133.004)

This is an extraction from Naganori Yamaguchi's NYLL ClassFieldTheory,
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/IdealQuotients.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/IdealQuotients.lean),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The original file has
SHA-256 `8c7082cb0e2e8ac6db22ff1afd4a1d173032246eac681ed075bb9feab7c5f71e`.
The readable original is in the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`. Attribution is also
registered as `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The published errata directory contains no applicable NYLL entry.

## Source correspondence

Every original name below is in `LocalFieldTheory`; every adapted name is
in `Langlands.NYLL.LocalFieldTheory`.

| Unit | Original name | Source declaration lines | Adapted name |
| --- | --- | --- | --- |
| M133.001 | `integerRingModMaximalIdealAddEquivResidue` | 27–30 | `integerRingModMaximalIdealAddEquivResidue` |
| M133.004 | `chosenIntegerRingUniformizer` | 50–53 | `chosenIntegerRingUniformizer` |

Both use the arbitrary universe `u`, an explicit `(K : Type u)`, then
instance arguments `[Field K] [ValuativeRel K]`, in that order.
The uniformizer additionally has `[TopologicalSpace K]` followed by
`[IsNonarchimedeanLocalField K]`. No argument is added, removed, reordered
or changed between explicit, implicit and instance binding.

The first definition has type
`(𝒪[K] ⧸ (𝓂[K] : Ideal 𝒪[K])) ≃+ 𝓀[K]` and body `AddEquiv.refl _`.
Mathlib's residue field is definitionally that quotient, so this is the
actual additive identity equivalence. The second returns an element of
`𝒪[K]` with the exact body
`Classical.choose (IsDiscreteValuationRing.exists_irreducible 𝒪[K])`.
The DVR instance is Mathlib's canonical instance for the supplied local
field. This preserves the source choice, rather than introducing an
extra uniformizer parameter or a new DVR instance. The definitions retain
the source's `noncomputable section`.

## Reuse and modifications

The only import is `Mathlib.NumberTheory.LocalField.Basic`. It supplies
the actual integer ring, residue field, maximal ideal, local-field class
and DVR instance. The source's `PrincipalUnitQuotients` and cardinal
imports are unnecessary for these two constructions and are omitted.
No same-named implementation was found in the current Library or Mathlib.
Existing Mathlib constructions `AddEquiv.refl` and
`IsDiscreteValuationRing.exists_irreducible` are used directly.

Worker 201 extracted exactly these two source definitions, prefixed their
namespace with `Langlands.NYLL`, shortened their docstrings, reduced the
imports and wrote this Markdown on 13 November 2026. The definition
bodies, result types, universes and parameter telescopes are unchanged.
No theorem proof, private helper, anonymous command, instance, notation,
or original-namespace alias is introduced. In particular, the facts that
the chosen element is irreducible and generates the maximal ideal are
separate proposition targets, not proofs supplied by this file.

## Attribution

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi, all rights reserved; authors Naganori Yamaguchi
(assisted by OpenAI Codex); Apache-2.0. The original
[LICENSE](../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and [NOTICE](../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
remain in `licenses/NYLL/`. No private port or compatibility patch is
reused. This file supplies supporting local-field data and claims no host
class-formation or reciprocity result.
