# Uniformizer valuation and maximal-ideal power targets (M133)

These are exact proposition targets extracted from Naganori Yamaguchi's
NYLL ClassFieldTheory,
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/IdealQuotients.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/IdealQuotients.lean),
pinned at `fbd320cd8b1b06487c58227e92eb135794267709`. The original file
SHA-256 is `8c7082cb0e2e8ac6db22ff1afd4a1d173032246eac681ed075bb9feab7c5f71e`.
The readable registered snapshot is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement
is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum is present in the published errata directory.

## Exact name map and source statements

Original names are in `LocalFieldTheory`; adapted names are in
`Langlands.NYLL.LocalFieldTheory`. Ranges run from the source theorem
command through its proposition, before its proof.

| Unit | Original theorem | Source statement lines | Adapted Prop definition |
| --- | --- | --- | --- |
| M133.005 | `chosenIntegerRingUniformizer_irreducible` | 56–59 | `chosenIntegerRingUniformizer_irreducibleStatement` |
| M133.006 | `chosenIntegerRingUniformizer_maximalIdeal_eq` | 63–66 | `chosenIntegerRingUniformizer_maximalIdeal_eqStatement` |
| M133.014 | `valueGroupWithZeroIsoInt_of_integerRing_irreducible` | 166–172 | `valueGroupWithZeroIsoInt_of_integerRing_irreducibleStatement` |
| M133.015 | `v_integerRingIrreducibleFieldUnit` | 212–216 | `v_integerRingIrreducibleFieldUnitStatement` |
| M133.016 | `v_integerRingIrreducibleFieldUnit_inv` | 237–241 | `v_integerRingIrreducibleFieldUnit_invStatement` |
| M133.020 | `exists_chosenIntegerRingUniformizer_pow_mul_mem_integerRing` | 294–298 | `exists_chosenIntegerRingUniformizer_pow_mul_mem_integerRingStatement` |
| M133.021 | `maximalIdeal_pow_eq_span_uniformizer_pow_of_irreducible` | 346–349 | `maximalIdeal_pow_eq_span_uniformizer_pow_of_irreducibleStatement` |
| M133.022 | `maximalIdeal_pow_eq_span_uniformizer_pow` | 353–357 | `maximalIdeal_pow_eq_span_uniformizer_powStatement` |
| M133.023 | `mul_uniformizer_pow_mem_maximalIdeal_pow` | 363–367 | `mul_uniformizer_pow_mem_maximalIdeal_powStatement` |
| M133.024 | `mul_uniformizer_pow_mem_maximalIdeal_pow_succ_iff` | 374–379 | `mul_uniformizer_pow_mem_maximalIdeal_pow_succ_iffStatement` |

All ten targets retain the arbitrary universe `u` and the complete
source prefix, in order:

```lean
(K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]
```

The rest of each telescope is preserved as follows. These are explicit
binders, including each named proof hypothesis.

| Source units | Remaining binders, in order |
| --- | --- |
| .005, .006 | none |
| .014 | `(ϖ : 𝒪[K]) (hϖ : Irreducible ϖ)` |
| .015, .016 | `(ϖ : 𝒪[K]) (hϖ : Irreducible ϖ) (u : Kˣ) (hu : (u : K) = ((ϖ : 𝒪[K]) : K))` |
| .020 | `(x : K)` |
| .021 | `(ϖ : 𝒪[K]) (hϖ : Irreducible ϖ) (n : Nat)` |
| .022 | `(n : Nat)` |
| .023, .024 | `(ϖ : 𝒪[K]) (hϖ : Irreducible ϖ) (n : Nat) (r : 𝒪[K])` |

The first two targets say the actual chosen element is irreducible and
generates the actual maximal ideal. Target .014 says that any integer-ring
irreducible has multiplicative value `ofAdd (-1)` under Mathlib's
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt`. Targets .015 and
.016 use the published NYLL normalized additive function `v`: a field unit
represented by that irreducible has value `-1`, and its inverse has value
`1`. The equality hypothesis `hu` is retained in each telescope even though
it does not occur in the body. No sign reversal or comparison with a
separately supplied host valuation is made.

Target .020 is the original denominator-clearing existence statement:
for each `x : K` some natural power of the chosen element, coerced to `K`,
makes the product integral. Targets .021–.022 identify maximal-ideal
powers with the spans of powers of an arbitrary irreducible and of the
chosen irreducible respectively. Target .023 puts `r * ϖ ^ n` into the
`n`-th ideal power. Target .024 says that this element lies in power
`n + 1` exactly when `r` is in the maximal ideal. Natural powers, actual
ideal membership and the order of multiplication are all unchanged.
The explicit `hϖ` hypotheses in .014–.016/.021/.023/.024 remain arguments
of the definitions even where the proposition body does not use them.

## Reuse and complete modification record

The imports are the paired `IdealQuotients.Definitions` data module and
the published NYLL `Basic.Definitions` containing
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v` (M128.001).
Their Mathlib dependencies supply the actual valuation, integer ring,
maximal ideal, residue field and local-field class. No replacement
interface or additional hypothesis is introduced. The selected statement
types need no private source lemma or other unpublished NYLL declaration.
No same-named statement was found in the current Library or Mathlib.

Worker 201 extracted these ten theorem types, changed `theorem name : P`
to `def nameStatement : Prop := P`, prefixed their namespace with
`Langlands.NYLL`, and omitted all theorem proofs. References to the source
`LocalFieldTheory.IsNonarchimedeanLocalField.v` use its published
`Langlands.NYLL` counterpart. The Mathlib isomorphism is qualified with
`_root_` to avoid collision with the adapted NYLL namespace. Imports were
reduced from the source principal-unit/cardinal closure to the two modules
above; source theorem docstrings were replaced by unit labels. The
source's `noncomputable section` is unnecessary for these Prop-valued
bodies and is omitted. There are no other modifications to universes,
binder kinds, binder order, source hypotheses or proposition bodies.
No proof, new axiom, instance, original-namespace alias, private helper
or anonymous command is included. These are statements only; their
proofs are separate work.

## Attribution and scope

The source copyright/author header is retained verbatim: copyright 2026
Naganori Yamaguchi, all rights reserved; authors Naganori Yamaguchi
(assisted by OpenAI Codex); Apache-2.0. The original
[LICENSE](../../../../../../licenses/NYLL/LICENSE), SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and [NOTICE](../../../../../../licenses/NYLL/NOTICE), SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
remain unchanged in `licenses/NYLL/`. This extraction uses the original
source directly and reuses no private draft or compatibility patch.
These local-field support targets claim no class-formation, cup,
transfer, Tate-cohomology or reciprocity result. M133.058 is outside this
file and awaits its separately routed principal-unit quotient definition.
